// Lean compiler output
// Module: Init.Meta
// Imports: public import Init.Meta.Defs public meta import Init.Meta.Defs public meta import Init.Syntax
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
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpLemma;
extern lean_object* l_Lean_Parser_Tactic_simpErase;
extern lean_object* l_Lean_Parser_Tactic_discharger;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
extern lean_object* l_Lean_Parser_Tactic_location;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Tactic_simpStar;
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
size_t lean_array_size(lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value;
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addPrec"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(197, 68, 23, 63, 244, 39, 18, 227)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrec"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 162, 64, 41, 156, 201, 248, 85)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termEval__prec___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termEval_prec_"};
static const lean_object* l_Lean_termEval__prec___00__closed__0 = (const lean_object*)&l_Lean_termEval__prec___00__closed__0_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termEval__prec___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__1_value_aux_0),((lean_object*)&l_Lean_termEval__prec___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 225, 125, 23, 245, 187, 1, 255)}};
static const lean_object* l_Lean_termEval__prec___00__closed__1 = (const lean_object*)&l_Lean_termEval__prec___00__closed__1_value;
static const lean_string_object l_Lean_termEval__prec___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termEval__prec___00__closed__2 = (const lean_object*)&l_Lean_termEval__prec___00__closed__2_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termEval__prec___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termEval__prec___00__closed__3 = (const lean_object*)&l_Lean_termEval__prec___00__closed__3_value;
static const lean_string_object l_Lean_termEval__prec___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eval_prec "};
static const lean_object* l_Lean_termEval__prec___00__closed__4 = (const lean_object*)&l_Lean_termEval__prec___00__closed__4_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__4_value)}};
static const lean_object* l_Lean_termEval__prec___00__closed__5 = (const lean_object*)&l_Lean_termEval__prec___00__closed__5_value;
static const lean_string_object l_Lean_termEval__prec___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prec"};
static const lean_object* l_Lean_termEval__prec___00__closed__6 = (const lean_object*)&l_Lean_termEval__prec___00__closed__6_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termEval__prec___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(178, 133, 204, 73, 239, 123, 12, 87)}};
static const lean_object* l_Lean_termEval__prec___00__closed__7 = (const lean_object*)&l_Lean_termEval__prec___00__closed__7_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__7_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_termEval__prec___00__closed__8 = (const lean_object*)&l_Lean_termEval__prec___00__closed__8_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_termEval__prec___00__closed__5_value),((lean_object*)&l_Lean_termEval__prec___00__closed__8_value)}};
static const lean_object* l_Lean_termEval__prec___00__closed__9 = (const lean_object*)&l_Lean_termEval__prec___00__closed__9_value;
static const lean_ctor_object l_Lean_termEval__prec___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termEval__prec___00__closed__9_value)}};
static const lean_object* l_Lean_termEval__prec___00__closed__10 = (const lean_object*)&l_Lean_termEval__prec___00__closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_termEval__prec__ = (const lean_object*)&l_Lean_termEval__prec___00__closed__10_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addPrio"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 218, 70, 150, 87, 9, 79, 160)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrio"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 12, 102, 115, 130, 88, 1, 102)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termEval__prio___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termEval_prio_"};
static const lean_object* l_Lean_termEval__prio___00__closed__0 = (const lean_object*)&l_Lean_termEval__prio___00__closed__0_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termEval__prio___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termEval__prio___00__closed__1_value_aux_0),((lean_object*)&l_Lean_termEval__prio___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 155, 229, 233, 248, 162, 206, 174)}};
static const lean_object* l_Lean_termEval__prio___00__closed__1 = (const lean_object*)&l_Lean_termEval__prio___00__closed__1_value;
static const lean_string_object l_Lean_termEval__prio___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eval_prio "};
static const lean_object* l_Lean_termEval__prio___00__closed__2 = (const lean_object*)&l_Lean_termEval__prio___00__closed__2_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termEval__prio___00__closed__2_value)}};
static const lean_object* l_Lean_termEval__prio___00__closed__3 = (const lean_object*)&l_Lean_termEval__prio___00__closed__3_value;
static const lean_string_object l_Lean_termEval__prio___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_termEval__prio___00__closed__4 = (const lean_object*)&l_Lean_termEval__prio___00__closed__4_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termEval__prio___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_termEval__prio___00__closed__5 = (const lean_object*)&l_Lean_termEval__prio___00__closed__5_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termEval__prio___00__closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_termEval__prio___00__closed__6 = (const lean_object*)&l_Lean_termEval__prio___00__closed__6_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_termEval__prio___00__closed__3_value),((lean_object*)&l_Lean_termEval__prio___00__closed__6_value)}};
static const lean_object* l_Lean_termEval__prio___00__closed__7 = (const lean_object*)&l_Lean_termEval__prio___00__closed__7_value;
static const lean_ctor_object l_Lean_termEval__prio___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termEval__prio___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termEval__prio___00__closed__7_value)}};
static const lean_object* l_Lean_termEval__prio___00__closed__8 = (const lean_object*)&l_Lean_termEval__prio___00__closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_termEval__prio__ = (const lean_object*)&l_Lean_termEval__prio___00__closed__8_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticErw___"};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(209, 238, 24, 88, 158, 88, 125, 211)}};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "erw"};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticErw_______00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticErw_______00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__6;
static const lean_string_object l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticErw_______00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticErw_______00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticErw_______00__closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticErw______;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "valConfigItem"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 67, 19, 169, 17, 95, 109, 188)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transparency"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(185, 88, 49, 212, 108, 152, 53, 137)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value;
static const lean_array_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpAllKind"};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 105, 142, 36, 223, 225, 123, 184)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllKind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__15_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllKind___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllKind___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_simpAllKind = (const lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic_dsimpKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpKind"};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 20, 82, 166, 5, 15, 155, 11)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_dsimpKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpKind___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_dsimpKind = (const lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareSimpLikeTactic"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 29, 238, 199, 239, 152, 213, 112)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declare_simp_like_tactic"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__18_value),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value;
static const lean_string_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value;
static const lean_ctor_object l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termEval__prec___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value),((lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30_value;
static lean_once_cell_t l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31;
static lean_once_cell_t l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_declareSimpLikeTactic;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expandSimp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value),LEAN_SCALAR_PTR_LITERAL(130, 4, 119, 76, 201, 38, 241, 189)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "s.setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_value),LEAN_SCALAR_PTR_LITERAL(10, 5, 190, 174, 53, 198, 104, 96)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "s.setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_value),LEAN_SCALAR_PTR_LITERAL(51, 18, 73, 41, 18, 128, 68, 244)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkAtomFrom"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_value),LEAN_SCALAR_PTR_LITERAL(92, 136, 63, 126, 134, 85, 56, 129)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 207, 191, 201, 123, 75, 165)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "appendConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value),LEAN_SCALAR_PTR_LITERAL(211, 122, 231, 137, 224, 73, 76, 35)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "s.mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_value),LEAN_SCALAR_PTR_LITERAL(32, 59, 47, 97, 193, 185, 105, 5)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 202, 61, 94, 207, 219, 212, 185)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(248, 36, 244, 101, 120, 63, 145, 134)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(233, 186, 255, 143, 150, 72, 152, 71)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nonReserved"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 78, 166, 169, 121, 44, 215, 226)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\" only\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\" [\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stx_,*"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(168, 173, 54, 129, 112, 44, 137, 241)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_<|>_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(198, 97, 122, 56, 37, 186, 212, 102)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(228, 131, 5, 197, 58, 233, 166, 1)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<|>"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(201, 118, 35, 111, 187, 212, 189, 166)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(15, 91, 119, 34, 57, 38, 207, 78)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ",*"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"]\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(101, 206, 14, 113, 158, 249, 116, 159)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 231, 142, 150, 112, 103, 109, 218)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_dsimpKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 53, 215, 155, 171, 182, 123, 76)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\"dsimp\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(28, 85, 114, 99, 119, 142, 252, 55)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\"simp_all\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\"simp\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 205, 236, 180, 188, 29, 173, 240)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simp! "};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__6;
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " only"};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__10;
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__12_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__14;
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__17_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__19;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_simpAutoUnfold___closed__20_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__21;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__22;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__23;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__24;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAutoUnfold___closed__25;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAutoUnfold;
static const lean_string_object l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoUnfold"};
static const lean_object* l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value;
static lean_once_cell_t l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_;
static const lean_ctor_object l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(77, 69, 213, 1, 0, 109, 154, 151)}};
static const lean_object* l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_simpArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpArith"};
static const lean_object* l_Lean_Parser_Tactic_simpArith___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 47, 198, 44, 197, 94, 244, 200)}};
static const lean_object* l_Lean_Parser_Tactic_simpArith___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpArith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simp_arith "};
static const lean_object* l_Lean_Parser_Tactic_simpArith___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpArith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpArith___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpArith___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArith___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArith___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpArith;
static const lean_string_object l_Lean_Parser_Tactic_simpArithBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpArithBang"};
static const lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpArithBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 151, 237, 27, 117, 76, 215, 64)}};
static const lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpArithBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simp_arith! "};
static const lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpArithBang___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpArithBang___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_simpArithBang___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpArithBang___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpArithBang;
static const lean_string_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 140, 78, 27, 53, 62, 238, 147)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simp_all! "};
static const lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAllAutoUnfold;
static const lean_string_object l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_simpAllArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllArith"};
static const lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 202, 96, 76, 254, 39, 20, 47)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllArith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simp_all_arith"};
static const lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArith___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArith___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArith___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAllArith;
static const lean_string_object l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpAllArithBang"};
static const lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 196, 181, 251, 41, 107, 56, 49)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "simp_all_arith!"};
static const lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_simpAllArithBang___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_simpAllArithBang___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_simpAllArithBang___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_simpAllArithBang;
static const lean_string_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dsimpAutoUnfold"};
static const lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 242, 55, 207, 18, 232, 241, 249)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dsimp! "};
static const lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_dsimpAutoUnfold;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec_ref(v_a_11_);
lean_dec(v_x_10_);
v___x_15_ = lean_box(1);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_a_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
lean_inc_ref(v_a_11_);
v___x_19_ = l_Lean_evalPrec(v___x_18_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref(v___x_19_);
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_10_, v___x_22_);
lean_dec(v_x_10_);
v___x_24_ = l_Lean_evalPrec(v___x_23_, v_a_11_, v_a_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_37_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_37_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_30_ = lean_nat_add(v_a_20_, v_a_25_);
lean_dec(v_a_25_);
lean_dec(v_a_20_);
v___x_31_ = l_Nat_reprFast(v___x_30_);
v___x_32_ = lean_box(2);
v___x_33_ = l_Lean_Syntax_mkNumLit(v___x_31_, v___x_32_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_33_);
v___x_35_ = v___x_28_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_a_26_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
lean_dec(v_a_20_);
v_a_38_ = lean_ctor_get(v___x_24_, 0);
v_a_39_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_24_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_inc(v_a_38_);
lean_dec(v___x_24_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_38_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
else
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec_ref(v_a_11_);
lean_dec(v_x_10_);
v_a_47_ = lean_ctor_get(v___x_19_, 0);
v_a_48_ = lean_ctor_get(v___x_19_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_19_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_inc(v_a_47_);
lean_dec(v___x_19_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_47_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1));
lean_inc(v_x_62_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_x_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref(v_a_63_);
lean_dec(v_x_62_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_64_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l_Lean_Syntax_getArg(v_x_62_, v___x_69_);
lean_inc_ref(v_a_63_);
v___x_71_ = l_Lean_evalPrec(v___x_70_, v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
v_a_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_a_73_);
lean_dec_ref(v___x_71_);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = l_Lean_Syntax_getArg(v_x_62_, v___x_74_);
lean_dec(v_x_62_);
v___x_76_ = l_Lean_evalPrec(v___x_75_, v_a_63_, v_a_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_89_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_a_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_89_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_82_ = lean_nat_sub(v_a_72_, v_a_77_);
lean_dec(v_a_77_);
lean_dec(v_a_72_);
v___x_83_ = l_Nat_reprFast(v___x_82_);
v___x_84_ = lean_box(2);
v___x_85_ = l_Lean_Syntax_mkNumLit(v___x_83_, v___x_84_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_85_);
v___x_87_ = v___x_80_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_a_78_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_a_72_);
v_a_90_ = lean_ctor_get(v___x_76_, 0);
v_a_91_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_76_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_inc(v_a_90_);
lean_dec(v___x_76_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_a_63_);
lean_dec(v_x_62_);
v_a_99_ = lean_ctor_get(v___x_71_, 0);
v_a_100_ = lean_ctor_get(v___x_71_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_71_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_inc(v_a_99_);
lean_dec(v___x_71_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_99_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__1));
lean_inc(v_x_133_);
v___x_137_ = l_Lean_Syntax_isOfKind(v_x_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec_ref(v_a_134_);
lean_dec(v_x_133_);
v___x_138_ = lean_box(1);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_135_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = l_Lean_Syntax_getArg(v_x_133_, v___x_140_);
lean_dec(v_x_133_);
v___x_142_ = l_Lean_evalPrec(v___x_141_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_154_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_a_144_ = lean_ctor_get(v___x_142_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_154_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_148_ = l_Nat_reprFast(v_a_143_);
v___x_149_ = lean_box(2);
v___x_150_ = l_Lean_Syntax_mkNumLit(v___x_148_, v___x_149_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_a_144_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_155_ = lean_ctor_get(v___x_142_, 0);
v_a_156_ = lean_ctor_get(v___x_142_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_142_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_inc(v_a_155_);
lean_dec(v___x_142_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1));
lean_inc(v_x_170_);
v___x_174_ = l_Lean_Syntax_isOfKind(v_x_170_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_a_171_);
lean_dec(v_x_170_);
v___x_175_ = lean_box(1);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_172_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l_Lean_Syntax_getArg(v_x_170_, v___x_177_);
lean_inc_ref(v_a_171_);
v___x_179_ = l_Lean_evalPrio(v___x_178_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
v_a_181_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_a_181_);
lean_dec_ref(v___x_179_);
v___x_182_ = lean_unsigned_to_nat(2u);
v___x_183_ = l_Lean_Syntax_getArg(v_x_170_, v___x_182_);
lean_dec(v_x_170_);
v___x_184_ = l_Lean_evalPrio(v___x_183_, v_a_171_, v_a_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_a_186_ = lean_ctor_get(v___x_184_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_197_ == 0)
{
v___x_188_ = v___x_184_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_190_ = lean_nat_add(v_a_180_, v_a_185_);
lean_dec(v_a_185_);
lean_dec(v_a_180_);
v___x_191_ = l_Nat_reprFast(v___x_190_);
v___x_192_ = lean_box(2);
v___x_193_ = l_Lean_Syntax_mkNumLit(v___x_191_, v___x_192_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_193_);
v___x_195_ = v___x_188_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_a_186_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_180_);
v_a_198_ = lean_ctor_get(v___x_184_, 0);
v_a_199_ = lean_ctor_get(v___x_184_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_184_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_inc(v_a_198_);
lean_dec(v___x_184_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_a_171_);
lean_dec(v_x_170_);
v_a_207_ = lean_ctor_get(v___x_179_, 0);
v_a_208_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_179_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_inc(v_a_207_);
lean_dec(v___x_179_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1));
lean_inc(v_x_222_);
v___x_226_ = l_Lean_Syntax_isOfKind(v_x_222_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v_a_223_);
lean_dec(v_x_222_);
v___x_227_ = lean_box(1);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_a_224_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Lean_Syntax_getArg(v_x_222_, v___x_229_);
lean_inc_ref(v_a_223_);
v___x_231_ = l_Lean_evalPrio(v___x_230_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
v_a_233_ = lean_ctor_get(v___x_231_, 1);
lean_inc(v_a_233_);
lean_dec_ref(v___x_231_);
v___x_234_ = lean_unsigned_to_nat(2u);
v___x_235_ = l_Lean_Syntax_getArg(v_x_222_, v___x_234_);
lean_dec(v_x_222_);
v___x_236_ = l_Lean_evalPrio(v___x_235_, v_a_223_, v_a_233_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_a_238_ = lean_ctor_get(v___x_236_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_249_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_242_ = lean_nat_sub(v_a_232_, v_a_237_);
lean_dec(v_a_237_);
lean_dec(v_a_232_);
v___x_243_ = l_Nat_reprFast(v___x_242_);
v___x_244_ = lean_box(2);
v___x_245_ = l_Lean_Syntax_mkNumLit(v___x_243_, v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_245_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_a_238_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_232_);
v_a_250_ = lean_ctor_get(v___x_236_, 0);
v_a_251_ = lean_ctor_get(v___x_236_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_236_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_inc(v_a_250_);
lean_dec(v___x_236_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_a_223_);
lean_dec(v_x_222_);
v_a_259_ = lean_ctor_get(v___x_231_, 0);
v_a_260_ = lean_ctor_get(v___x_231_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_231_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_inc(v_a_259_);
lean_dec(v___x_231_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_259_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(lean_object* v_x_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_termEval__prio___00__closed__1));
lean_inc(v_x_290_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_x_290_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_a_291_);
lean_dec(v_x_290_);
v___x_295_ = lean_box(1);
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_292_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = l_Lean_Syntax_getArg(v_x_290_, v___x_297_);
lean_dec(v_x_290_);
v___x_299_ = l_Lean_evalPrio(v___x_298_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_a_301_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_311_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_305_ = l_Nat_reprFast(v_a_300_);
v___x_306_ = lean_box(2);
v___x_307_ = l_Lean_Syntax_mkNumLit(v___x_305_, v___x_306_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_307_);
v___x_309_ = v___x_303_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_a_301_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_299_, 0);
v_a_313_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_299_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_inc(v_a_312_);
lean_dec(v___x_299_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = l_Lean_Parser_Tactic_optConfig;
v___x_333_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__4));
v___x_334_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_335_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_337_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__5, &l_Lean_Parser_Tactic_tacticErw_______00__closed__5_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5);
v___x_338_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_339_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_336_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = l_Lean_Parser_Tactic_location;
v___x_344_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_347_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__6, &l_Lean_Parser_Tactic_tacticErw_______00__closed__6_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6);
v___x_348_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_349_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__10, &l_Lean_Parser_Tactic_tacticErw_______00__closed__10_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10);
v___x_351_ = lean_unsigned_to_nat(1022u);
v___x_352_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__2));
v___x_353_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw______(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__11, &l_Lean_Parser_Tactic_tacticErw_______00__closed__11_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t v_sz_355_, size_t v_i_356_, lean_object* v_bs_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_356_, v_sz_355_);
if (v___x_358_ == 0)
{
return v_bs_357_;
}
else
{
lean_object* v_v_359_; lean_object* v___x_360_; lean_object* v_bs_x27_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; 
v_v_359_ = lean_array_uget(v_bs_357_, v_i_356_);
v___x_360_ = lean_unsigned_to_nat(0u);
v_bs_x27_361_ = lean_array_uset(v_bs_357_, v_i_356_, v___x_360_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_356_, v___x_362_);
v___x_364_ = lean_array_uset(v_bs_x27_361_, v_i_356_, v_v_359_);
v_i_356_ = v___x_363_;
v_bs_357_ = v___x_364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0___boxed(lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_bs_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_370_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_boxed_369_, v_i_boxed_370_, v_bs_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Array_mkArray0(lean_box(0));
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13));
v___x_404_ = l_String_toRawSubstring_x27(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21));
v___x_418_ = l_String_toRawSubstring_x27(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(lean_object* v_x_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__2));
lean_inc(v_x_439_);
v___x_443_ = l_Lean_Syntax_isOfKind(v_x_439_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v_a_440_);
lean_dec(v_x_439_);
v___x_444_ = lean_box(1);
v___x_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_463_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = l_Lean_Syntax_getArg(v_x_439_, v___x_446_);
v___x_448_ = lean_unsigned_to_nat(2u);
v___x_449_ = l_Lean_Syntax_getArg(v_x_439_, v___x_448_);
v___x_511_ = lean_unsigned_to_nat(3u);
v___x_512_ = l_Lean_Syntax_getArg(v_x_439_, v___x_511_);
lean_dec(v_x_439_);
v___x_513_ = l_Lean_Syntax_getOptional_x3f(v___x_512_);
lean_dec(v___x_512_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
v___y_463_ = v___x_514_;
goto v___jp_462_;
}
else
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_val_515_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_513_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v___x_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_val_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
v___y_463_ = v___x_520_;
goto v___jp_462_;
}
}
}
v___jp_450_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = l_Array_append___redArg(v___y_453_, v___y_457_);
lean_dec_ref(v___y_457_);
lean_inc(v___y_451_);
v___x_459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_459_, 0, v___y_451_);
lean_ctor_set(v___x_459_, 1, v___y_454_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
v___x_460_ = l_Lean_Syntax_node4(v___y_451_, v___y_455_, v___y_456_, v___y_452_, v___x_449_, v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_a_441_);
return v___x_461_;
}
v___jp_462_:
{
lean_object* v_quotContext_464_; lean_object* v_currMacroScope_465_; lean_object* v_ref_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; size_t v_sz_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_quotContext_464_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_quotContext_464_);
v_currMacroScope_465_ = lean_ctor_get(v_a_440_, 2);
lean_inc(v_currMacroScope_465_);
v_ref_466_ = lean_ctor_get(v_a_440_, 5);
lean_inc(v_ref_466_);
lean_dec_ref(v_a_440_);
v___x_467_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_468_ = 0;
v___x_469_ = l_Lean_SourceInfo_fromRef(v_ref_466_, v___x_468_);
lean_dec(v_ref_466_);
v___x_470_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3));
v___x_471_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4));
lean_inc(v___x_469_);
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_474_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
v___x_475_ = l_Lean_Parser_Tactic_getConfigItems(v___x_447_);
v_sz_476_ = lean_array_size(v___x_475_);
v___x_477_ = ((size_t)0ULL);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_476_, v___x_477_, v___x_475_);
v___x_479_ = l_Array_append___redArg(v___x_474_, v___x_478_);
lean_dec_ref(v___x_478_);
v___x_480_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_481_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_482_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___x_469_);
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_469_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14);
v___x_485_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15));
lean_inc(v_currMacroScope_465_);
lean_inc(v_quotContext_464_);
v___x_486_ = l_Lean_addMacroScope(v_quotContext_464_, v___x_485_, v_currMacroScope_465_);
v___x_487_ = lean_box(0);
lean_inc(v___x_469_);
v___x_488_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_488_, 0, v___x_469_);
lean_ctor_set(v___x_488_, 1, v___x_484_);
lean_ctor_set(v___x_488_, 2, v___x_486_);
lean_ctor_set(v___x_488_, 3, v___x_487_);
v___x_489_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___x_469_);
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_469_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19));
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20));
lean_inc(v___x_469_);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_469_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22);
v___x_495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23));
v___x_496_ = l_Lean_addMacroScope(v_quotContext_464_, v___x_495_, v_currMacroScope_465_);
v___x_497_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29));
lean_inc(v___x_469_);
v___x_498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_498_, 0, v___x_469_);
lean_ctor_set(v___x_498_, 1, v___x_494_);
lean_ctor_set(v___x_498_, 2, v___x_496_);
lean_ctor_set(v___x_498_, 3, v___x_497_);
lean_inc(v___x_469_);
v___x_499_ = l_Lean_Syntax_node2(v___x_469_, v___x_491_, v___x_493_, v___x_498_);
v___x_500_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___x_469_);
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_469_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
lean_inc(v___x_469_);
v___x_502_ = l_Lean_Syntax_node5(v___x_469_, v___x_481_, v___x_483_, v___x_488_, v___x_490_, v___x_499_, v___x_501_);
lean_inc(v___x_469_);
v___x_503_ = l_Lean_Syntax_node1(v___x_469_, v___x_480_, v___x_502_);
v___x_504_ = lean_array_push(v___x_479_, v___x_503_);
lean_inc(v___x_469_);
v___x_505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_505_, 0, v___x_469_);
lean_ctor_set(v___x_505_, 1, v___x_473_);
lean_ctor_set(v___x_505_, 2, v___x_504_);
lean_inc(v___x_469_);
v___x_506_ = l_Lean_Syntax_node1(v___x_469_, v___x_467_, v___x_505_);
if (lean_obj_tag(v___y_463_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___y_451_ = v___x_469_;
v___y_452_ = v___x_506_;
v___y_453_ = v___x_474_;
v___y_454_ = v___x_473_;
v___y_455_ = v___x_470_;
v___y_456_ = v___x_472_;
v___y_457_ = v___x_507_;
goto v___jp_450_;
}
else
{
lean_object* v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_val_508_ = lean_ctor_get(v___y_463_, 0);
lean_inc(v_val_508_);
lean_dec_ref(v___y_463_);
v___x_509_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___x_510_ = lean_array_push(v___x_509_, v_val_508_);
v___y_451_ = v___x_469_;
v___y_452_ = v___x_506_;
v___y_453_ = v___x_474_;
v___y_454_ = v___x_473_;
v___y_455_ = v___x_470_;
v___y_456_ = v___x_472_;
v___y_457_ = v___x_510_;
goto v___jp_450_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = l_Lean_Parser_Tactic_optConfig;
v___x_683_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30));
v___x_684_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_685_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_682_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31);
v___x_687_ = lean_unsigned_to_nat(1022u);
v___x_688_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
v___x_689_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
lean_ctor_set(v___x_689_, 2, v___x_686_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(lean_object* v_____do__lift_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = 0;
v___x_695_ = l_Lean_SourceInfo_fromRef(v_____do__lift_691_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___y_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0___boxed(lean_object* v_____do__lift_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_____do__lift_697_, v___y_698_, v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v_____do__lift_697_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14));
v___x_717_ = l_String_toRawSubstring_x27(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20));
v___x_725_ = l_String_toRawSubstring_x27(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26));
v___x_733_ = l_String_toRawSubstring_x27(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36));
v___x_745_ = l_String_toRawSubstring_x27(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49));
v___x_760_ = l_String_toRawSubstring_x27(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53));
v___x_767_ = l_String_toRawSubstring_x27(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64));
v___x_783_ = l_String_toRawSubstring_x27(v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66));
v___x_786_ = l_String_toRawSubstring_x27(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73));
v___x_796_ = l_String_toRawSubstring_x27(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__13));
v___x_800_ = l_String_toRawSubstring_x27(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83));
v___x_816_ = l_String_toRawSubstring_x27(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86));
v___x_821_ = l_String_toRawSubstring_x27(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v___x_836_, lean_object* v___x_837_, lean_object* v_____x_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_snd_841_; lean_object* v_fst_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_1109_; 
v_snd_841_ = lean_ctor_get(v_____x_838_, 1);
v_fst_842_ = lean_ctor_get(v_____x_838_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_____x_838_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_844_ = v_____x_838_;
v_isShared_845_ = v_isSharedCheck_1109_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_842_);
lean_dec(v_____x_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_1109_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_1108_; 
v_fst_846_ = lean_ctor_get(v_snd_841_, 0);
v_snd_847_ = lean_ctor_get(v_snd_841_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_snd_841_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_849_ = v_snd_841_;
v_isShared_850_ = v_isSharedCheck_1108_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_846_);
lean_dec(v_snd_841_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_1108_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_quotContext_851_; lean_object* v_currMacroScope_852_; lean_object* v_ref_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v_quotContext_851_ = lean_ctor_get(v___y_839_, 1);
lean_inc(v_quotContext_851_);
v_currMacroScope_852_ = lean_ctor_get(v___y_839_, 2);
lean_inc(v_currMacroScope_852_);
v_ref_853_ = lean_ctor_get(v___y_839_, 5);
lean_inc(v_ref_853_);
lean_dec_ref(v___y_839_);
v___x_854_ = 0;
v___x_855_ = l_Lean_SourceInfo_fromRef(v_ref_853_, v___x_854_);
lean_dec(v_ref_853_);
v___x_856_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_857_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_858_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_859_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_861_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_860_);
v___x_862_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
lean_inc(v___x_855_);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___x_855_);
lean_ctor_set(v___x_863_, 1, v___x_856_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_865_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_866_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4));
lean_inc(v___x_855_);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 2);
lean_ctor_set(v___x_849_, 1, v___x_867_);
lean_ctor_set(v___x_849_, 0, v___x_855_);
v___x_869_ = v___x_849_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_1107_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_870_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_871_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_873_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_872_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_874_ = l_Lean_Syntax_node1(v___x_855_, v___x_873_, v___x_863_);
v___x_875_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7));
v___x_876_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_877_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_875_, v___x_876_);
lean_inc(v___x_855_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 2);
lean_ctor_set(v___x_844_, 1, v___x_876_);
lean_ctor_set(v___x_844_, 0, v___x_855_);
v___x_879_ = v___x_844_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_876_);
v___x_879_ = v_reuseFailAlloc_1106_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc(v___x_855_);
v___x_880_ = l_Lean_Syntax_node2(v___x_855_, v___x_877_, v___x_879_, v___x_832_);
lean_inc(v___x_855_);
v___x_881_ = l_Lean_Syntax_node2(v___x_855_, v___x_871_, v___x_874_, v___x_880_);
lean_inc(v___x_855_);
v___x_882_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9));
lean_inc(v___x_855_);
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_855_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_inc_ref(v___x_884_);
lean_inc(v___x_855_);
v___x_885_ = l_Lean_Syntax_node3(v___x_855_, v___x_866_, v___x_869_, v___x_882_, v___x_884_);
lean_inc(v___x_855_);
v___x_886_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v___x_885_);
v___x_887_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_888_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_887_);
lean_inc(v___x_855_);
v___x_889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_855_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_inc(v___x_855_);
v___x_890_ = l_Lean_Syntax_node1(v___x_855_, v___x_888_, v___x_889_);
lean_inc(v___x_855_);
v___x_891_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v___x_890_);
lean_inc_ref_n(v___x_863_, 5);
lean_inc(v___x_855_);
v___x_892_ = l_Lean_Syntax_node7(v___x_855_, v___x_861_, v___x_863_, v___x_886_, v___x_863_, v___x_863_, v___x_891_, v___x_863_, v___x_863_);
v___x_893_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_894_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12));
lean_inc(v___x_855_);
v___x_896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_855_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_898_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15);
v___x_900_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_901_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_900_, v_currMacroScope_852_);
v___x_902_ = lean_box(0);
lean_inc(v___x_855_);
v___x_903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_903_, 0, v___x_855_);
lean_ctor_set(v___x_903_, 1, v___x_899_);
lean_ctor_set(v___x_903_, 2, v___x_901_);
lean_ctor_set(v___x_903_, 3, v___x_902_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_904_ = l_Lean_Syntax_node2(v___x_855_, v___x_898_, v___x_903_, v___x_863_);
v___x_905_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_906_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_908_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
lean_inc(v___x_855_);
v___x_910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_855_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20));
v___x_912_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21);
v___x_913_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_914_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_913_, v_currMacroScope_852_);
lean_inc_ref(v___x_830_);
v___x_915_ = l_Lean_Name_mkStr2(v___x_830_, v___x_911_);
lean_inc(v___x_915_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_902_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_902_);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
lean_inc(v___x_855_);
v___x_920_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_920_, 0, v___x_855_);
lean_ctor_set(v___x_920_, 1, v___x_912_);
lean_ctor_set(v___x_920_, 2, v___x_914_);
lean_ctor_set(v___x_920_, 3, v___x_919_);
lean_inc(v___x_855_);
v___x_921_ = l_Lean_Syntax_node2(v___x_855_, v___x_908_, v___x_910_, v___x_920_);
lean_inc(v___x_855_);
v___x_922_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v___x_921_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_923_ = l_Lean_Syntax_node2(v___x_855_, v___x_906_, v___x_863_, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_925_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_857_, v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___x_855_);
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_855_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_929_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_928_);
lean_inc(v___x_855_);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_855_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v___x_931_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_932_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_931_);
v___x_933_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27);
v___x_934_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_935_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_934_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_936_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_936_, 0, v___x_855_);
lean_ctor_set(v___x_936_, 1, v___x_933_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_ctor_set(v___x_936_, 3, v___x_902_);
lean_inc_ref(v___x_936_);
lean_inc(v___x_855_);
v___x_937_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v___x_936_);
v___x_938_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29));
lean_inc(v___x_855_);
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_855_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_941_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_940_);
lean_inc(v___x_855_);
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_855_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
v___x_943_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_944_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_946_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_945_);
v___x_947_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_948_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34));
lean_inc(v___x_855_);
v___x_950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_855_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_952_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_951_);
v___x_953_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37);
v___x_954_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_955_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_954_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_956_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_956_, 0, v___x_855_);
lean_ctor_set(v___x_956_, 1, v___x_953_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v___x_902_);
v___x_957_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39));
lean_inc(v___x_855_);
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_855_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_960_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_959_);
v___x_961_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_962_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_961_);
v___x_963_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42));
lean_inc(v___x_855_);
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_855_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_inc_ref(v___x_833_);
v___x_965_ = l_String_toRawSubstring_x27(v___x_833_);
v___x_966_ = l_Lean_Name_mkStr1(v___x_833_);
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_967_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_966_, v_currMacroScope_852_);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_834_);
lean_ctor_set(v___x_968_, 1, v___x_902_);
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_902_);
lean_inc(v___x_855_);
v___x_970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_970_, 0, v___x_855_);
lean_ctor_set(v___x_970_, 1, v___x_965_);
lean_ctor_set(v___x_970_, 2, v___x_967_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43));
lean_inc(v___x_855_);
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_855_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___x_855_);
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_855_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_inc_ref(v___x_974_);
lean_inc(v___x_855_);
v___x_975_ = l_Lean_Syntax_node5(v___x_855_, v___x_962_, v___x_964_, v___x_970_, v___x_972_, v___x_835_, v___x_974_);
lean_inc(v___x_855_);
v___x_976_ = l_Lean_Syntax_node1(v___x_855_, v___x_960_, v___x_975_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_956_);
lean_inc(v___x_855_);
v___x_977_ = l_Lean_Syntax_node4(v___x_855_, v___x_952_, v___x_956_, v___x_863_, v___x_958_, v___x_976_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_950_);
lean_inc(v___x_855_);
v___x_978_ = l_Lean_Syntax_node3(v___x_855_, v___x_948_, v___x_950_, v___x_863_, v___x_977_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_946_);
lean_inc(v___x_855_);
v___x_979_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_978_, v___x_863_);
v___x_980_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_981_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_983_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_985_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_987_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_986_);
lean_inc_ref(v___x_936_);
lean_inc(v___x_855_);
v___x_988_ = l_Lean_Syntax_node1(v___x_855_, v___x_987_, v___x_936_);
v___x_989_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_990_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_989_);
v___x_991_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50);
v___x_992_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_993_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_992_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_994_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_994_, 0, v___x_855_);
lean_ctor_set(v___x_994_, 1, v___x_991_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
lean_ctor_set(v___x_994_, 3, v___x_902_);
lean_inc(v___x_855_);
v___x_995_ = l_Lean_Syntax_node1(v___x_855_, v___x_856_, v_fst_842_);
lean_inc(v___x_990_);
lean_inc(v___x_855_);
v___x_996_ = l_Lean_Syntax_node2(v___x_855_, v___x_990_, v___x_994_, v___x_995_);
lean_inc_ref(v___x_927_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___x_988_);
lean_inc(v___x_985_);
lean_inc(v___x_855_);
v___x_997_ = l_Lean_Syntax_node5(v___x_855_, v___x_985_, v___x_988_, v___x_863_, v___x_863_, v___x_927_, v___x_996_);
lean_inc(v___x_983_);
lean_inc(v___x_855_);
v___x_998_ = l_Lean_Syntax_node1(v___x_855_, v___x_983_, v___x_997_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_950_);
lean_inc(v___x_981_);
lean_inc(v___x_855_);
v___x_999_ = l_Lean_Syntax_node3(v___x_855_, v___x_981_, v___x_950_, v___x_863_, v___x_998_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_946_);
lean_inc(v___x_855_);
v___x_1000_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_999_, v___x_863_);
v___x_1001_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54);
v___x_1002_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1003_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1002_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_1004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1004_, 0, v___x_855_);
lean_ctor_set(v___x_1004_, 1, v___x_1001_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_ctor_set(v___x_1004_, 3, v___x_902_);
v___x_1005_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58));
v___x_1006_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59));
lean_inc(v___x_855_);
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_855_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_inc(v___x_855_);
v___x_1008_ = l_Lean_Syntax_node1(v___x_855_, v___x_1005_, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1010_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1012_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___x_855_);
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_855_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63));
v___x_1016_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65);
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1017_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_836_, v_currMacroScope_852_);
lean_inc_ref(v___x_837_);
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1018_ = l_Lean_Name_mkStr3(v___x_830_, v___x_831_, v___x_837_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_902_);
lean_inc(v___x_855_);
v___x_1021_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1021_, 0, v___x_855_);
lean_ctor_set(v___x_1021_, 1, v___x_1016_);
lean_ctor_set(v___x_1021_, 2, v___x_1017_);
lean_ctor_set(v___x_1021_, 3, v___x_1020_);
lean_inc(v___x_855_);
v___x_1022_ = l_Lean_Syntax_node1(v___x_855_, v___x_1015_, v___x_1021_);
lean_inc_ref(v___x_1014_);
lean_inc(v___x_855_);
v___x_1023_ = l_Lean_Syntax_node2(v___x_855_, v___x_1012_, v___x_1014_, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66));
v___x_1025_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67);
v___x_1026_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1027_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1026_, v_currMacroScope_852_);
lean_inc_ref(v___x_830_);
v___x_1028_ = l_Lean_Name_mkStr2(v___x_830_, v___x_1024_);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_902_);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_902_);
lean_inc(v___x_855_);
v___x_1031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1031_, 0, v___x_855_);
lean_ctor_set(v___x_1031_, 1, v___x_1025_);
lean_ctor_set(v___x_1031_, 2, v___x_1027_);
lean_ctor_set(v___x_1031_, 3, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70));
v___x_1033_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71));
lean_inc(v___x_855_);
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_855_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
lean_inc_ref(v___x_884_);
lean_inc(v___x_1008_);
lean_inc_ref(v___x_1034_);
lean_inc_ref(v___x_936_);
lean_inc(v___x_855_);
v___x_1035_ = l_Lean_Syntax_node4(v___x_855_, v___x_1032_, v___x_936_, v___x_1034_, v___x_1008_, v___x_884_);
v___x_1036_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1037_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74);
v___x_1039_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1040_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1039_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_1041_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1041_, 0, v___x_855_);
lean_ctor_set(v___x_1041_, 1, v___x_1038_);
lean_ctor_set(v___x_1041_, 2, v___x_1040_);
lean_ctor_set(v___x_1041_, 3, v___x_902_);
v___x_1042_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76);
v___x_1043_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1044_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1043_, v_currMacroScope_852_);
v___x_1045_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81));
lean_inc(v___x_855_);
v___x_1046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1046_, 0, v___x_855_);
lean_ctor_set(v___x_1046_, 1, v___x_1042_);
lean_ctor_set(v___x_1046_, 2, v___x_1044_);
lean_ctor_set(v___x_1046_, 3, v___x_1045_);
lean_inc_ref(v___x_974_);
lean_inc_ref(v___x_927_);
lean_inc(v___x_855_);
v___x_1047_ = l_Lean_Syntax_node5(v___x_855_, v___x_1037_, v___x_1014_, v___x_1041_, v___x_927_, v___x_1046_, v___x_974_);
lean_inc(v___x_855_);
v___x_1048_ = l_Lean_Syntax_node3(v___x_855_, v___x_856_, v___x_1035_, v_fst_846_, v___x_1047_);
lean_inc(v___x_990_);
lean_inc(v___x_855_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_855_, v___x_990_, v___x_1031_, v___x_1048_);
lean_inc_ref(v___x_974_);
lean_inc(v___x_1023_);
lean_inc(v___x_1010_);
lean_inc(v___x_855_);
v___x_1050_ = l_Lean_Syntax_node3(v___x_855_, v___x_1010_, v___x_1023_, v___x_1049_, v___x_974_);
lean_inc(v___x_855_);
v___x_1051_ = l_Lean_Syntax_node2(v___x_855_, v___x_856_, v___x_1008_, v___x_1050_);
lean_inc_ref(v___x_1004_);
lean_inc(v___x_990_);
lean_inc(v___x_855_);
v___x_1052_ = l_Lean_Syntax_node2(v___x_855_, v___x_990_, v___x_1004_, v___x_1051_);
lean_inc_ref(v___x_927_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___x_988_);
lean_inc(v___x_985_);
lean_inc(v___x_855_);
v___x_1053_ = l_Lean_Syntax_node5(v___x_855_, v___x_985_, v___x_988_, v___x_863_, v___x_863_, v___x_927_, v___x_1052_);
lean_inc(v___x_983_);
lean_inc(v___x_855_);
v___x_1054_ = l_Lean_Syntax_node1(v___x_855_, v___x_983_, v___x_1053_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_950_);
lean_inc(v___x_981_);
lean_inc(v___x_855_);
v___x_1055_ = l_Lean_Syntax_node3(v___x_855_, v___x_981_, v___x_950_, v___x_863_, v___x_1054_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_946_);
lean_inc(v___x_855_);
v___x_1056_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_1055_, v___x_863_);
v___x_1057_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82));
lean_inc(v___x_855_);
v___x_1058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_855_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
lean_inc(v___x_855_);
v___x_1059_ = l_Lean_Syntax_node1(v___x_855_, v___x_1005_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83));
v___x_1061_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84);
v___x_1062_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_1063_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1062_, v_currMacroScope_852_);
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1064_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_837_, v___x_1060_);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_902_);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_902_);
lean_inc(v___x_855_);
v___x_1067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1067_, 0, v___x_855_);
lean_ctor_set(v___x_1067_, 1, v___x_1061_);
lean_ctor_set(v___x_1067_, 2, v___x_1063_);
lean_ctor_set(v___x_1067_, 3, v___x_1066_);
lean_inc(v___x_1059_);
lean_inc(v___x_855_);
v___x_1068_ = l_Lean_Syntax_node4(v___x_855_, v___x_1032_, v___x_936_, v___x_1034_, v___x_1059_, v___x_884_);
lean_inc(v___x_855_);
v___x_1069_ = l_Lean_Syntax_node2(v___x_855_, v___x_856_, v___x_1068_, v___x_956_);
lean_inc(v___x_990_);
lean_inc(v___x_855_);
v___x_1070_ = l_Lean_Syntax_node2(v___x_855_, v___x_990_, v___x_1067_, v___x_1069_);
lean_inc(v___x_855_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_855_, v___x_1010_, v___x_1023_, v___x_1070_, v___x_974_);
lean_inc(v___x_855_);
v___x_1072_ = l_Lean_Syntax_node2(v___x_855_, v___x_856_, v___x_1059_, v___x_1071_);
lean_inc(v___x_855_);
v___x_1073_ = l_Lean_Syntax_node2(v___x_855_, v___x_990_, v___x_1004_, v___x_1072_);
lean_inc_ref(v___x_927_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___x_988_);
lean_inc(v___x_985_);
lean_inc(v___x_855_);
v___x_1074_ = l_Lean_Syntax_node5(v___x_855_, v___x_985_, v___x_988_, v___x_863_, v___x_863_, v___x_927_, v___x_1073_);
lean_inc(v___x_983_);
lean_inc(v___x_855_);
v___x_1075_ = l_Lean_Syntax_node1(v___x_855_, v___x_983_, v___x_1074_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_950_);
lean_inc(v___x_981_);
lean_inc(v___x_855_);
v___x_1076_ = l_Lean_Syntax_node3(v___x_855_, v___x_981_, v___x_950_, v___x_863_, v___x_1075_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_946_);
lean_inc(v___x_855_);
v___x_1077_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_1076_, v___x_863_);
v___x_1078_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87);
v___x_1079_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89));
v___x_1080_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_1079_, v_currMacroScope_852_);
lean_inc(v___x_855_);
v___x_1081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1081_, 0, v___x_855_);
lean_ctor_set(v___x_1081_, 1, v___x_1078_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
lean_ctor_set(v___x_1081_, 3, v___x_902_);
lean_inc_ref(v___x_927_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___x_855_);
v___x_1082_ = l_Lean_Syntax_node5(v___x_855_, v___x_985_, v___x_988_, v___x_863_, v___x_863_, v___x_927_, v___x_1081_);
lean_inc(v___x_855_);
v___x_1083_ = l_Lean_Syntax_node1(v___x_855_, v___x_983_, v___x_1082_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_1084_ = l_Lean_Syntax_node3(v___x_855_, v___x_981_, v___x_950_, v___x_863_, v___x_1083_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_946_);
lean_inc(v___x_855_);
v___x_1085_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_1084_, v___x_863_);
v___x_1086_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90));
lean_inc_ref(v___x_831_);
lean_inc_ref(v___x_830_);
v___x_1087_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_864_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91));
lean_inc(v___x_855_);
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_855_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
lean_inc(v___x_937_);
lean_inc(v___x_855_);
v___x_1090_ = l_Lean_Syntax_node2(v___x_855_, v___x_1087_, v___x_1089_, v___x_937_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_1091_ = l_Lean_Syntax_node2(v___x_855_, v___x_946_, v___x_1090_, v___x_863_);
lean_inc(v___x_855_);
v___x_1092_ = l_Lean_Syntax_node6(v___x_855_, v___x_856_, v___x_979_, v___x_1000_, v___x_1056_, v___x_1077_, v___x_1085_, v___x_1091_);
lean_inc(v___x_855_);
v___x_1093_ = l_Lean_Syntax_node1(v___x_855_, v___x_944_, v___x_1092_);
lean_inc(v___x_855_);
v___x_1094_ = l_Lean_Syntax_node2(v___x_855_, v___x_941_, v___x_942_, v___x_1093_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_1095_ = l_Lean_Syntax_node4(v___x_855_, v___x_932_, v___x_937_, v___x_863_, v___x_939_, v___x_1094_);
lean_inc(v___x_855_);
v___x_1096_ = l_Lean_Syntax_node2(v___x_855_, v___x_929_, v___x_930_, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92));
v___x_1098_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93));
v___x_1099_ = l_Lean_Name_mkStr4(v___x_830_, v___x_831_, v___x_1097_, v___x_1098_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___x_855_);
v___x_1100_ = l_Lean_Syntax_node2(v___x_855_, v___x_1099_, v___x_863_, v___x_863_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_855_);
v___x_1101_ = l_Lean_Syntax_node4(v___x_855_, v___x_925_, v___x_927_, v___x_1096_, v___x_1100_, v___x_863_);
lean_inc(v___x_855_);
v___x_1102_ = l_Lean_Syntax_node5(v___x_855_, v___x_894_, v___x_896_, v___x_904_, v___x_923_, v___x_1101_, v___x_863_);
lean_inc(v___x_855_);
v___x_1103_ = l_Lean_Syntax_node2(v___x_855_, v___x_859_, v___x_892_, v___x_1102_);
v___x_1104_ = l_Lean_Syntax_node2(v___x_855_, v___x_856_, v_snd_847_, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___y_840_);
return v___x_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(uint8_t v___x_1110_, lean_object* v_____do__lift_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1111_, v___x_1110_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(lean_object* v___x_1116_, lean_object* v_____do__lift_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___x_39912__boxed_1120_; lean_object* v_res_1121_; 
v___x_39912__boxed_1120_ = lean_unbox(v___x_1116_);
v_res_1121_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_39912__boxed_1120_, v_____do__lift_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_____do__lift_1117_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1137_ = l_String_toRawSubstring_x27(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11));
v___x_1150_ = l_String_toRawSubstring_x27(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25));
v___x_1176_ = l_String_toRawSubstring_x27(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30));
v___x_1187_ = l_String_toRawSubstring_x27(v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34));
v___x_1197_ = l_String_toRawSubstring_x27(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40));
v___x_1209_ = l_String_toRawSubstring_x27(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44));
v___x_1219_ = l_String_toRawSubstring_x27(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_1230_ = l_String_toRawSubstring_x27(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58));
v___x_1253_ = l_String_toRawSubstring_x27(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_1270_ = l_String_toRawSubstring_x27(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(lean_object* v_x_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___y_1289_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1299_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0));
v___x_1300_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1));
v___x_1301_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__0));
v___x_1302_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
lean_inc(v_x_1285_);
v___x_1303_ = l_Lean_Syntax_isOfKind(v_x_1285_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_a_1286_);
lean_dec(v_x_1285_);
v___x_1304_ = lean_box(1);
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_a_1287_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1742_; lean_object* v___x_1881_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = l_Lean_Syntax_getArg(v_x_1285_, v___x_1306_);
v___x_1308_ = lean_unsigned_to_nat(2u);
v___x_1309_ = l_Lean_Syntax_getArg(v_x_1285_, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(4u);
v___x_1311_ = l_Lean_Syntax_getArg(v_x_1285_, v___x_1310_);
v___x_1312_ = lean_unsigned_to_nat(6u);
v___x_1313_ = l_Lean_Syntax_getArg(v_x_1285_, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(8u);
v___x_1315_ = l_Lean_Syntax_getArg(v_x_1285_, v___x_1314_);
lean_dec(v_x_1285_);
v___x_1316_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1317_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_1318_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27));
v___x_1319_ = lean_box(0);
v___x_1881_ = l_Lean_Syntax_getOptional_x3f(v___x_1307_);
lean_dec(v___x_1307_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_box(0);
v___y_1742_ = v___x_1882_;
goto v___jp_1741_;
}
else
{
lean_object* v_val_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_val_1883_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_val_1883_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_val_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v___y_1742_ = v___x_1888_;
goto v___jp_1741_;
}
}
}
v___jp_1320_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc_ref(v___y_1329_);
v___x_1336_ = l_Array_append___redArg(v___y_1329_, v___y_1335_);
lean_dec_ref(v___y_1335_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1321_);
lean_ctor_set(v___x_1337_, 1, v___y_1325_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___y_1321_);
lean_ctor_set(v___x_1338_, 1, v___y_1325_);
lean_ctor_set(v___x_1338_, 2, v___y_1329_);
v___x_1339_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
v___x_1340_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1333_, v___x_1339_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1341_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1340_, v___x_1338_);
lean_inc(v___y_1321_);
v___x_1342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___y_1321_);
lean_ctor_set(v___x_1342_, 1, v___y_1332_);
v___x_1343_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
v___x_1344_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1334_, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___y_1321_);
v___x_1346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___y_1321_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
lean_inc(v___y_1321_);
v___x_1348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___y_1321_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___y_1321_);
v___x_1350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___y_1321_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___y_1321_);
v___x_1352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___y_1321_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
lean_inc_ref(v___x_1352_);
lean_inc(v___x_1311_);
lean_inc_ref(v___x_1346_);
lean_inc(v___y_1321_);
v___x_1353_ = l_Lean_Syntax_node5(v___y_1321_, v___x_1344_, v___x_1346_, v___x_1348_, v___x_1350_, v___x_1311_, v___x_1352_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1354_ = l_Lean_Syntax_node1(v___y_1321_, v___y_1325_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
lean_inc(v___y_1321_);
v___x_1356_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1355_, v___x_1313_);
v___x_1357_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1358_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1359_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1360_ = l_Lean_addMacroScope(v___y_1330_, v___x_1359_, v___y_1327_);
lean_inc(v___y_1328_);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1317_);
lean_ctor_set(v___x_1361_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1363_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1321_);
lean_ctor_set(v___x_1363_, 1, v___x_1358_);
lean_ctor_set(v___x_1363_, 2, v___x_1360_);
lean_ctor_set(v___x_1363_, 3, v___x_1362_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1364_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1363_, v___x_1338_);
v___x_1365_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1366_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1367_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1368_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1369_ = l_Lean_addMacroScope(v___y_1330_, v___x_1368_, v___y_1327_);
v___x_1370_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
lean_inc(v___y_1328_);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1321_);
lean_ctor_set(v___x_1373_, 1, v___x_1367_);
lean_ctor_set(v___x_1373_, 2, v___x_1369_);
lean_ctor_set(v___x_1373_, 3, v___x_1372_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1374_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1373_, v___x_1338_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1375_ = l_Lean_Syntax_node1(v___y_1321_, v___y_1325_, v___x_1374_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v___x_1346_);
lean_inc(v___y_1321_);
v___x_1376_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1366_, v___x_1346_, v___x_1375_, v___x_1352_);
v___x_1377_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
lean_inc(v___y_1321_);
v___x_1378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1321_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_inc_ref(v___x_1378_);
lean_inc(v___y_1321_);
v___x_1379_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1365_, v___x_1376_, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1381_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
lean_inc(v___y_1321_);
v___x_1382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___y_1321_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
lean_inc(v___y_1321_);
v___x_1384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___y_1321_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
lean_inc(v___y_1321_);
v___x_1385_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1318_, v___x_1384_);
lean_inc(v___y_1321_);
v___x_1386_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1380_, v___x_1382_, v___x_1385_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1387_ = l_Lean_Syntax_node1(v___y_1321_, v___y_1325_, v___x_1386_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v___x_1346_);
lean_inc(v___y_1321_);
v___x_1388_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1366_, v___x_1346_, v___x_1387_, v___x_1352_);
lean_inc_ref(v___x_1378_);
lean_inc(v___y_1321_);
v___x_1389_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1365_, v___x_1388_, v___x_1378_);
v___x_1390_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
lean_inc(v___y_1321_);
v___x_1391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1321_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_inc(v___y_1321_);
v___x_1392_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1318_, v___x_1391_);
lean_inc(v___y_1321_);
v___x_1393_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1355_, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1395_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1396_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
v___x_1397_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1398_ = l_Lean_addMacroScope(v___y_1330_, v___x_1397_, v___y_1327_);
v___x_1399_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28));
lean_inc(v___y_1328_);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1402_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1402_, 0, v___y_1321_);
lean_ctor_set(v___x_1402_, 1, v___x_1396_);
lean_ctor_set(v___x_1402_, 2, v___x_1398_);
lean_ctor_set(v___x_1402_, 3, v___x_1401_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1403_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1402_, v___x_1338_);
v___x_1404_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
lean_inc(v___y_1321_);
v___x_1405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1321_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1407_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1408_ = l_Lean_addMacroScope(v___y_1330_, v___x_1407_, v___y_1327_);
v___x_1409_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
lean_inc(v___y_1328_);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1412_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1321_);
lean_ctor_set(v___x_1412_, 1, v___x_1406_);
lean_ctor_set(v___x_1412_, 2, v___x_1408_);
lean_ctor_set(v___x_1412_, 3, v___x_1411_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1413_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1412_, v___x_1338_);
v___x_1414_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1415_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1416_ = l_Lean_addMacroScope(v___y_1330_, v___x_1415_, v___y_1327_);
v___x_1417_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
lean_inc(v___y_1328_);
v___x_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1420_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1420_, 0, v___y_1321_);
lean_ctor_set(v___x_1420_, 1, v___x_1414_);
lean_ctor_set(v___x_1420_, 2, v___x_1416_);
lean_ctor_set(v___x_1420_, 3, v___x_1419_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1421_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1420_, v___x_1338_);
lean_inc_ref(v___x_1405_);
lean_inc(v___y_1321_);
v___x_1422_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1395_, v___x_1413_, v___x_1405_, v___x_1421_);
lean_inc(v___y_1321_);
v___x_1423_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1395_, v___x_1403_, v___x_1405_, v___x_1422_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1424_ = l_Lean_Syntax_node1(v___y_1321_, v___y_1325_, v___x_1423_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v___x_1346_);
lean_inc(v___y_1321_);
v___x_1425_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1366_, v___x_1346_, v___x_1424_, v___x_1352_);
v___x_1426_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
lean_inc(v___y_1321_);
v___x_1427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1321_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_inc(v___y_1321_);
v___x_1428_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1394_, v___x_1425_, v___x_1427_);
v___x_1429_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
lean_inc(v___y_1321_);
v___x_1430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1321_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc(v___y_1321_);
v___x_1431_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1318_, v___x_1430_);
lean_inc(v___y_1321_);
v___x_1432_ = l_Lean_Syntax_node1(v___y_1321_, v___x_1355_, v___x_1431_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1433_ = l_Lean_Syntax_node3(v___y_1321_, v___y_1325_, v___x_1393_, v___x_1428_, v___x_1432_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v___x_1346_);
lean_inc(v___y_1321_);
v___x_1434_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1366_, v___x_1346_, v___x_1433_, v___x_1352_);
lean_inc_ref(v___x_1378_);
lean_inc(v___y_1321_);
v___x_1435_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1365_, v___x_1434_, v___x_1378_);
v___x_1436_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
v___x_1437_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
lean_inc(v___y_1327_);
lean_inc(v___y_1330_);
v___x_1438_ = l_Lean_addMacroScope(v___y_1330_, v___x_1437_, v___y_1327_);
v___x_1439_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43));
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___y_1328_);
lean_inc(v___y_1331_);
v___x_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___y_1331_);
lean_inc(v___y_1321_);
v___x_1442_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1442_, 0, v___y_1321_);
lean_ctor_set(v___x_1442_, 1, v___x_1436_);
lean_ctor_set(v___x_1442_, 2, v___x_1438_);
lean_ctor_set(v___x_1442_, 3, v___x_1441_);
lean_inc_ref(v___x_1338_);
lean_inc(v___y_1321_);
v___x_1443_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1357_, v___x_1442_, v___x_1338_);
lean_inc(v___y_1325_);
lean_inc(v___y_1321_);
v___x_1444_ = l_Lean_Syntax_node1(v___y_1321_, v___y_1325_, v___x_1443_);
lean_inc(v___y_1321_);
v___x_1445_ = l_Lean_Syntax_node3(v___y_1321_, v___x_1366_, v___x_1346_, v___x_1444_, v___x_1352_);
lean_inc(v___y_1321_);
v___x_1446_ = l_Lean_Syntax_node2(v___y_1321_, v___x_1365_, v___x_1445_, v___x_1378_);
lean_inc(v___y_1321_);
v___x_1447_ = l_Lean_Syntax_node6(v___y_1321_, v___y_1325_, v___x_1356_, v___x_1364_, v___x_1379_, v___x_1389_, v___x_1435_, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
lean_inc(v___y_1321_);
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1321_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1451_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1452_ = l_Lean_addMacroScope(v___y_1330_, v___x_1451_, v___y_1327_);
lean_inc(v___y_1321_);
v___x_1453_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1321_);
lean_ctor_set(v___x_1453_, 1, v___x_1450_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
lean_ctor_set(v___x_1453_, 3, v___y_1331_);
v___x_1454_ = lean_unsigned_to_nat(10u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_array_push(v___x_1455_, v___x_1337_);
lean_inc_ref(v___x_1338_);
v___x_1457_ = lean_array_push(v___x_1456_, v___x_1338_);
v___x_1458_ = lean_array_push(v___x_1457_, v___x_1341_);
v___x_1459_ = lean_array_push(v___x_1458_, v___x_1342_);
lean_inc_ref(v___x_1338_);
v___x_1460_ = lean_array_push(v___x_1459_, v___x_1338_);
v___x_1461_ = lean_array_push(v___x_1460_, v___x_1354_);
v___x_1462_ = lean_array_push(v___x_1461_, v___x_1338_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1447_);
v___x_1464_ = lean_array_push(v___x_1463_, v___x_1449_);
v___x_1465_ = lean_array_push(v___x_1464_, v___x_1453_);
v___x_1466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1321_);
lean_ctor_set(v___x_1466_, 1, v___y_1326_);
lean_ctor_set(v___x_1466_, 2, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1323_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1324_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1299_, v___x_1300_, v___x_1311_, v___x_1316_, v___x_1317_, v___x_1315_, v___x_1319_, v___x_1301_, v___x_1468_, v_a_1286_, v___y_1322_);
v___y_1289_ = v___x_1469_;
goto v___jp_1288_;
}
v___jp_1470_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_inc_ref(v___y_1474_);
v___x_1486_ = l_Array_append___redArg(v___y_1474_, v___y_1485_);
lean_dec_ref(v___y_1485_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1484_);
lean_ctor_set(v___x_1487_, 1, v___y_1480_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1484_);
lean_ctor_set(v___x_1488_, 1, v___y_1480_);
lean_ctor_set(v___x_1488_, 2, v___y_1474_);
v___x_1489_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
v___x_1490_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1471_, v___x_1489_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1491_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1490_, v___x_1488_);
lean_inc(v___y_1484_);
v___x_1492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1484_);
lean_ctor_set(v___x_1492_, 1, v___y_1479_);
v___x_1493_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
v___x_1494_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1478_, v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___y_1484_);
v___x_1496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1484_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
lean_inc(v___y_1484_);
v___x_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___y_1484_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___y_1484_);
v___x_1500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1484_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___y_1484_);
v___x_1502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1484_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
lean_inc_ref(v___x_1502_);
lean_inc(v___x_1311_);
lean_inc_ref(v___x_1496_);
lean_inc(v___y_1484_);
v___x_1503_ = l_Lean_Syntax_node5(v___y_1484_, v___x_1494_, v___x_1496_, v___x_1498_, v___x_1500_, v___x_1311_, v___x_1502_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1504_ = l_Lean_Syntax_node1(v___y_1484_, v___y_1480_, v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
lean_inc(v___y_1484_);
v___x_1506_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1505_, v___x_1313_);
v___x_1507_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1508_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1509_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v___x_1510_ = l_Lean_addMacroScope(v___y_1481_, v___x_1509_, v___y_1483_);
lean_inc(v___y_1476_);
v___x_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1317_);
lean_ctor_set(v___x_1511_, 1, v___y_1476_);
lean_inc(v___y_1475_);
v___x_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___y_1475_);
lean_inc(v___y_1484_);
v___x_1513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1513_, 0, v___y_1484_);
lean_ctor_set(v___x_1513_, 1, v___x_1508_);
lean_ctor_set(v___x_1513_, 2, v___x_1510_);
lean_ctor_set(v___x_1513_, 3, v___x_1512_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1514_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1507_, v___x_1513_, v___x_1488_);
v___x_1515_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1516_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1517_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1518_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v___x_1519_ = l_Lean_addMacroScope(v___y_1481_, v___x_1518_, v___y_1483_);
v___x_1520_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
lean_inc(v___y_1476_);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___y_1476_);
lean_inc(v___y_1475_);
v___x_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___y_1475_);
lean_inc(v___y_1484_);
v___x_1523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1523_, 0, v___y_1484_);
lean_ctor_set(v___x_1523_, 1, v___x_1517_);
lean_ctor_set(v___x_1523_, 2, v___x_1519_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1524_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1507_, v___x_1523_, v___x_1488_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1525_ = l_Lean_Syntax_node1(v___y_1484_, v___y_1480_, v___x_1524_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v___x_1496_);
lean_inc(v___y_1484_);
v___x_1526_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1516_, v___x_1496_, v___x_1525_, v___x_1502_);
v___x_1527_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
lean_inc(v___y_1484_);
v___x_1528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___y_1484_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
lean_inc_ref(v___x_1528_);
lean_inc(v___y_1484_);
v___x_1529_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1515_, v___x_1526_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1531_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
lean_inc(v___y_1484_);
v___x_1532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1484_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
lean_inc(v___y_1484_);
v___x_1534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1484_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
lean_inc(v___y_1484_);
v___x_1535_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1318_, v___x_1534_);
lean_inc(v___y_1484_);
v___x_1536_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1530_, v___x_1532_, v___x_1535_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1537_ = l_Lean_Syntax_node1(v___y_1484_, v___y_1480_, v___x_1536_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v___x_1496_);
lean_inc(v___y_1484_);
v___x_1538_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1516_, v___x_1496_, v___x_1537_, v___x_1502_);
lean_inc_ref(v___x_1528_);
lean_inc(v___y_1484_);
v___x_1539_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1515_, v___x_1538_, v___x_1528_);
v___x_1540_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
lean_inc(v___y_1484_);
v___x_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___y_1484_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
lean_inc(v___y_1484_);
v___x_1542_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1318_, v___x_1541_);
lean_inc(v___y_1484_);
v___x_1543_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1505_, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1545_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1546_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1547_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v___x_1548_ = l_Lean_addMacroScope(v___y_1481_, v___x_1547_, v___y_1483_);
v___x_1549_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
lean_inc(v___y_1476_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___y_1476_);
lean_inc(v___y_1475_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___y_1475_);
lean_inc(v___y_1484_);
v___x_1552_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1552_, 0, v___y_1484_);
lean_ctor_set(v___x_1552_, 1, v___x_1546_);
lean_ctor_set(v___x_1552_, 2, v___x_1548_);
lean_ctor_set(v___x_1552_, 3, v___x_1551_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1553_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1507_, v___x_1552_, v___x_1488_);
v___x_1554_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
lean_inc(v___y_1484_);
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___y_1484_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1557_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v___x_1558_ = l_Lean_addMacroScope(v___y_1481_, v___x_1557_, v___y_1483_);
v___x_1559_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
lean_inc(v___y_1476_);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___y_1476_);
lean_inc(v___y_1475_);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___y_1475_);
lean_inc(v___y_1484_);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v___y_1484_);
lean_ctor_set(v___x_1562_, 1, v___x_1556_);
lean_ctor_set(v___x_1562_, 2, v___x_1558_);
lean_ctor_set(v___x_1562_, 3, v___x_1561_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1563_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1507_, v___x_1562_, v___x_1488_);
lean_inc(v___y_1484_);
v___x_1564_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1545_, v___x_1553_, v___x_1555_, v___x_1563_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1565_ = l_Lean_Syntax_node1(v___y_1484_, v___y_1480_, v___x_1564_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v___x_1496_);
lean_inc(v___y_1484_);
v___x_1566_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1516_, v___x_1496_, v___x_1565_, v___x_1502_);
v___x_1567_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
lean_inc(v___y_1484_);
v___x_1568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___y_1484_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_inc(v___y_1484_);
v___x_1569_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1544_, v___x_1566_, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
lean_inc(v___y_1484_);
v___x_1571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___y_1484_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_inc(v___y_1484_);
v___x_1572_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1318_, v___x_1571_);
lean_inc(v___y_1484_);
v___x_1573_ = l_Lean_Syntax_node1(v___y_1484_, v___x_1505_, v___x_1572_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1574_ = l_Lean_Syntax_node3(v___y_1484_, v___y_1480_, v___x_1543_, v___x_1569_, v___x_1573_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v___x_1496_);
lean_inc(v___y_1484_);
v___x_1575_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1516_, v___x_1496_, v___x_1574_, v___x_1502_);
lean_inc_ref(v___x_1528_);
lean_inc(v___y_1484_);
v___x_1576_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1515_, v___x_1575_, v___x_1528_);
v___x_1577_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
v___x_1578_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v___x_1579_ = l_Lean_addMacroScope(v___y_1481_, v___x_1578_, v___y_1483_);
v___x_1580_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43));
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___y_1476_);
lean_inc(v___y_1475_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___y_1475_);
lean_inc(v___y_1484_);
v___x_1583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1583_, 0, v___y_1484_);
lean_ctor_set(v___x_1583_, 1, v___x_1577_);
lean_ctor_set(v___x_1583_, 2, v___x_1579_);
lean_ctor_set(v___x_1583_, 3, v___x_1582_);
lean_inc_ref(v___x_1488_);
lean_inc(v___y_1484_);
v___x_1584_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1507_, v___x_1583_, v___x_1488_);
lean_inc(v___y_1480_);
lean_inc(v___y_1484_);
v___x_1585_ = l_Lean_Syntax_node1(v___y_1484_, v___y_1480_, v___x_1584_);
lean_inc(v___y_1484_);
v___x_1586_ = l_Lean_Syntax_node3(v___y_1484_, v___x_1516_, v___x_1496_, v___x_1585_, v___x_1502_);
lean_inc(v___y_1484_);
v___x_1587_ = l_Lean_Syntax_node2(v___y_1484_, v___x_1515_, v___x_1586_, v___x_1528_);
lean_inc(v___y_1484_);
v___x_1588_ = l_Lean_Syntax_node6(v___y_1484_, v___y_1480_, v___x_1506_, v___x_1514_, v___x_1529_, v___x_1539_, v___x_1576_, v___x_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
lean_inc(v___y_1484_);
v___x_1590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1484_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1592_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1593_ = l_Lean_addMacroScope(v___y_1481_, v___x_1592_, v___y_1483_);
lean_inc(v___y_1484_);
v___x_1594_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1594_, 0, v___y_1484_);
lean_ctor_set(v___x_1594_, 1, v___x_1591_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
lean_ctor_set(v___x_1594_, 3, v___y_1475_);
v___x_1595_ = lean_unsigned_to_nat(10u);
v___x_1596_ = lean_mk_empty_array_with_capacity(v___x_1595_);
v___x_1597_ = lean_array_push(v___x_1596_, v___x_1487_);
lean_inc_ref(v___x_1488_);
v___x_1598_ = lean_array_push(v___x_1597_, v___x_1488_);
v___x_1599_ = lean_array_push(v___x_1598_, v___x_1491_);
v___x_1600_ = lean_array_push(v___x_1599_, v___x_1492_);
lean_inc_ref(v___x_1488_);
v___x_1601_ = lean_array_push(v___x_1600_, v___x_1488_);
v___x_1602_ = lean_array_push(v___x_1601_, v___x_1504_);
v___x_1603_ = lean_array_push(v___x_1602_, v___x_1488_);
v___x_1604_ = lean_array_push(v___x_1603_, v___x_1588_);
v___x_1605_ = lean_array_push(v___x_1604_, v___x_1590_);
v___x_1606_ = lean_array_push(v___x_1605_, v___x_1594_);
v___x_1607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1607_, 0, v___y_1484_);
lean_ctor_set(v___x_1607_, 1, v___y_1472_);
lean_ctor_set(v___x_1607_, 2, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___y_1477_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___y_1482_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1299_, v___x_1300_, v___x_1311_, v___x_1316_, v___x_1317_, v___x_1315_, v___x_1319_, v___x_1301_, v___x_1609_, v_a_1286_, v___y_1473_);
v___y_1289_ = v___x_1610_;
goto v___jp_1288_;
}
v___jp_1611_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_inc_ref(v___y_1619_);
v___x_1627_ = l_Array_append___redArg(v___y_1619_, v___y_1626_);
lean_dec_ref(v___y_1626_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1624_);
lean_ctor_set(v___x_1628_, 1, v___y_1612_);
lean_ctor_set(v___x_1628_, 2, v___x_1627_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1624_);
lean_ctor_set(v___x_1629_, 1, v___y_1612_);
lean_ctor_set(v___x_1629_, 2, v___y_1619_);
v___x_1630_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
v___x_1631_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1622_, v___x_1630_);
lean_inc_ref(v___x_1629_);
lean_inc(v___y_1624_);
v___x_1632_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1631_, v___x_1629_);
lean_inc(v___y_1624_);
v___x_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___y_1624_);
lean_ctor_set(v___x_1633_, 1, v___y_1623_);
v___x_1634_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
v___x_1635_ = l_Lean_Name_mkStr4(v___x_1299_, v___x_1300_, v___y_1614_, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___y_1624_);
v___x_1637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1624_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
lean_inc(v___y_1624_);
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1624_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___y_1624_);
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1624_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___y_1624_);
v___x_1643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___y_1624_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
lean_inc_ref(v___x_1643_);
lean_inc(v___x_1311_);
lean_inc_ref(v___x_1637_);
lean_inc(v___y_1624_);
v___x_1644_ = l_Lean_Syntax_node5(v___y_1624_, v___x_1635_, v___x_1637_, v___x_1639_, v___x_1641_, v___x_1311_, v___x_1643_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1645_ = l_Lean_Syntax_node1(v___y_1624_, v___y_1612_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
lean_inc(v___y_1624_);
v___x_1647_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1646_, v___x_1313_);
v___x_1648_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1649_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1650_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc(v___y_1618_);
lean_inc(v___y_1617_);
v___x_1651_ = l_Lean_addMacroScope(v___y_1617_, v___x_1650_, v___y_1618_);
lean_inc(v___y_1625_);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1317_);
lean_ctor_set(v___x_1652_, 1, v___y_1625_);
lean_inc(v___y_1615_);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___y_1615_);
lean_inc(v___y_1624_);
v___x_1654_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1654_, 0, v___y_1624_);
lean_ctor_set(v___x_1654_, 1, v___x_1649_);
lean_ctor_set(v___x_1654_, 2, v___x_1651_);
lean_ctor_set(v___x_1654_, 3, v___x_1653_);
lean_inc_ref(v___x_1629_);
lean_inc(v___y_1624_);
v___x_1655_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1648_, v___x_1654_, v___x_1629_);
v___x_1656_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1657_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1658_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1659_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
lean_inc(v___y_1618_);
lean_inc(v___y_1617_);
v___x_1660_ = l_Lean_addMacroScope(v___y_1617_, v___x_1659_, v___y_1618_);
v___x_1661_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
lean_inc(v___y_1625_);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___y_1625_);
lean_inc(v___y_1615_);
v___x_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___y_1615_);
lean_inc(v___y_1624_);
v___x_1664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1624_);
lean_ctor_set(v___x_1664_, 1, v___x_1658_);
lean_ctor_set(v___x_1664_, 2, v___x_1660_);
lean_ctor_set(v___x_1664_, 3, v___x_1663_);
lean_inc_ref(v___x_1629_);
lean_inc(v___y_1624_);
v___x_1665_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1648_, v___x_1664_, v___x_1629_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1666_ = l_Lean_Syntax_node1(v___y_1624_, v___y_1612_, v___x_1665_);
lean_inc_ref(v___x_1643_);
lean_inc_ref(v___x_1637_);
lean_inc(v___y_1624_);
v___x_1667_ = l_Lean_Syntax_node3(v___y_1624_, v___x_1657_, v___x_1637_, v___x_1666_, v___x_1643_);
v___x_1668_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
lean_inc(v___y_1624_);
v___x_1669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1624_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
lean_inc_ref(v___x_1669_);
lean_inc(v___y_1624_);
v___x_1670_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1656_, v___x_1667_, v___x_1669_);
v___x_1671_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1672_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
lean_inc(v___y_1624_);
v___x_1673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1624_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
lean_inc(v___y_1624_);
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1624_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
lean_inc(v___y_1624_);
v___x_1676_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1318_, v___x_1675_);
lean_inc(v___y_1624_);
v___x_1677_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1671_, v___x_1673_, v___x_1676_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1678_ = l_Lean_Syntax_node1(v___y_1624_, v___y_1612_, v___x_1677_);
lean_inc_ref(v___x_1643_);
lean_inc_ref(v___x_1637_);
lean_inc(v___y_1624_);
v___x_1679_ = l_Lean_Syntax_node3(v___y_1624_, v___x_1657_, v___x_1637_, v___x_1678_, v___x_1643_);
lean_inc_ref(v___x_1669_);
lean_inc(v___y_1624_);
v___x_1680_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1656_, v___x_1679_, v___x_1669_);
v___x_1681_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
lean_inc(v___y_1624_);
v___x_1682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___y_1624_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
lean_inc(v___y_1624_);
v___x_1683_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1318_, v___x_1682_);
lean_inc(v___y_1624_);
v___x_1684_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1646_, v___x_1683_);
v___x_1685_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1686_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1687_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1688_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
lean_inc(v___y_1618_);
lean_inc(v___y_1617_);
v___x_1689_ = l_Lean_addMacroScope(v___y_1617_, v___x_1688_, v___y_1618_);
v___x_1690_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
lean_inc(v___y_1625_);
v___x_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___y_1625_);
lean_inc(v___y_1615_);
v___x_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___y_1615_);
lean_inc(v___y_1624_);
v___x_1693_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1624_);
lean_ctor_set(v___x_1693_, 1, v___x_1687_);
lean_ctor_set(v___x_1693_, 2, v___x_1689_);
lean_ctor_set(v___x_1693_, 3, v___x_1692_);
lean_inc_ref(v___x_1629_);
lean_inc(v___y_1624_);
v___x_1694_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1648_, v___x_1693_, v___x_1629_);
v___x_1695_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
lean_inc(v___y_1624_);
v___x_1696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___y_1624_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1698_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
lean_inc(v___y_1618_);
lean_inc(v___y_1617_);
v___x_1699_ = l_Lean_addMacroScope(v___y_1617_, v___x_1698_, v___y_1618_);
v___x_1700_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v___y_1625_);
lean_inc(v___y_1615_);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___y_1615_);
lean_inc(v___y_1624_);
v___x_1703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1624_);
lean_ctor_set(v___x_1703_, 1, v___x_1697_);
lean_ctor_set(v___x_1703_, 2, v___x_1699_);
lean_ctor_set(v___x_1703_, 3, v___x_1702_);
lean_inc_ref(v___x_1629_);
lean_inc(v___y_1624_);
v___x_1704_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1648_, v___x_1703_, v___x_1629_);
lean_inc(v___y_1624_);
v___x_1705_ = l_Lean_Syntax_node3(v___y_1624_, v___x_1686_, v___x_1694_, v___x_1696_, v___x_1704_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1706_ = l_Lean_Syntax_node1(v___y_1624_, v___y_1612_, v___x_1705_);
lean_inc_ref(v___x_1643_);
lean_inc_ref(v___x_1637_);
lean_inc(v___y_1624_);
v___x_1707_ = l_Lean_Syntax_node3(v___y_1624_, v___x_1657_, v___x_1637_, v___x_1706_, v___x_1643_);
v___x_1708_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
lean_inc(v___y_1624_);
v___x_1709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___y_1624_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
lean_inc(v___y_1624_);
v___x_1710_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1685_, v___x_1707_, v___x_1709_);
v___x_1711_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
lean_inc(v___y_1624_);
v___x_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___y_1624_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
lean_inc(v___y_1624_);
v___x_1713_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1318_, v___x_1712_);
lean_inc(v___y_1624_);
v___x_1714_ = l_Lean_Syntax_node1(v___y_1624_, v___x_1646_, v___x_1713_);
lean_inc(v___y_1612_);
lean_inc(v___y_1624_);
v___x_1715_ = l_Lean_Syntax_node3(v___y_1624_, v___y_1612_, v___x_1684_, v___x_1710_, v___x_1714_);
lean_inc(v___y_1624_);
v___x_1716_ = l_Lean_Syntax_node3(v___y_1624_, v___x_1657_, v___x_1637_, v___x_1715_, v___x_1643_);
lean_inc(v___y_1624_);
v___x_1717_ = l_Lean_Syntax_node2(v___y_1624_, v___x_1656_, v___x_1716_, v___x_1669_);
lean_inc(v___y_1624_);
v___x_1718_ = l_Lean_Syntax_node5(v___y_1624_, v___y_1612_, v___x_1647_, v___x_1655_, v___x_1670_, v___x_1680_, v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
lean_inc(v___y_1624_);
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___y_1624_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1722_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1723_ = l_Lean_addMacroScope(v___y_1617_, v___x_1722_, v___y_1618_);
lean_inc(v___y_1624_);
v___x_1724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1724_, 0, v___y_1624_);
lean_ctor_set(v___x_1724_, 1, v___x_1721_);
lean_ctor_set(v___x_1724_, 2, v___x_1723_);
lean_ctor_set(v___x_1724_, 3, v___y_1615_);
v___x_1725_ = lean_unsigned_to_nat(10u);
v___x_1726_ = lean_mk_empty_array_with_capacity(v___x_1725_);
v___x_1727_ = lean_array_push(v___x_1726_, v___x_1628_);
lean_inc_ref(v___x_1629_);
v___x_1728_ = lean_array_push(v___x_1727_, v___x_1629_);
v___x_1729_ = lean_array_push(v___x_1728_, v___x_1632_);
v___x_1730_ = lean_array_push(v___x_1729_, v___x_1633_);
lean_inc_ref(v___x_1629_);
v___x_1731_ = lean_array_push(v___x_1730_, v___x_1629_);
v___x_1732_ = lean_array_push(v___x_1731_, v___x_1645_);
v___x_1733_ = lean_array_push(v___x_1732_, v___x_1629_);
v___x_1734_ = lean_array_push(v___x_1733_, v___x_1718_);
v___x_1735_ = lean_array_push(v___x_1734_, v___x_1720_);
v___x_1736_ = lean_array_push(v___x_1735_, v___x_1724_);
v___x_1737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1624_);
lean_ctor_set(v___x_1737_, 1, v___y_1613_);
lean_ctor_set(v___x_1737_, 2, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1621_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1616_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1299_, v___x_1300_, v___x_1311_, v___x_1316_, v___x_1317_, v___x_1315_, v___x_1319_, v___x_1301_, v___x_1739_, v_a_1286_, v___y_1620_);
v___y_1289_ = v___x_1740_;
goto v___jp_1288_;
}
v___jp_1741_:
{
uint8_t v___x_1743_; 
v___x_1743_ = l_Lean_Syntax_isNone(v___x_1309_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1744_ = l_Lean_Syntax_getArg(v___x_1309_, v___x_1306_);
lean_dec(v___x_1309_);
v___x_1745_ = l_Lean_Syntax_getKind(v___x_1744_);
v___x_1746_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__1));
v___x_1747_ = lean_name_eq(v___x_1745_, v___x_1746_);
lean_dec(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v_quotContext_1748_; lean_object* v_currMacroScope_1749_; lean_object* v_ref_1750_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1791_; 
v_quotContext_1748_ = lean_ctor_get(v_a_1286_, 1);
v_currMacroScope_1749_ = lean_ctor_get(v_a_1286_, 2);
v_ref_1750_ = lean_ctor_get(v_a_1286_, 5);
v___x_1751_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1747_, v_ref_1750_, v_a_1286_, v_a_1287_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_a_1753_ = lean_ctor_get(v___x_1751_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1755_ = v___x_1751_;
v_isShared_1756_ = v_isSharedCheck_1791_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1791_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1757_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1758_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1759_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1752_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 2);
lean_ctor_set(v___x_1755_, 1, v___x_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1752_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1789_; 
v___x_1762_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50);
v___x_1763_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51));
lean_inc(v_currMacroScope_1749_);
lean_inc(v_quotContext_1748_);
v___x_1764_ = l_Lean_addMacroScope(v_quotContext_1748_, v___x_1763_, v_currMacroScope_1749_);
v___x_1765_ = lean_box(0);
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54));
lean_inc(v_a_1752_);
v___x_1767_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1752_);
lean_ctor_set(v___x_1767_, 1, v___x_1762_);
lean_ctor_set(v___x_1767_, 2, v___x_1764_);
lean_ctor_set(v___x_1767_, 3, v___x_1766_);
lean_inc_ref(v___x_1761_);
v___x_1768_ = l_Lean_Syntax_node3(v_a_1752_, v___x_1758_, v___x_1761_, v___x_1761_, v___x_1767_);
v___x_1769_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1747_, v_ref_1750_, v_a_1286_, v_a_1753_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_a_1771_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55));
lean_inc(v_a_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 2);
lean_ctor_set(v___x_1773_, 1, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1770_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = l_Lean_Syntax_node1(v_a_1770_, v___x_1318_, v___x_1777_);
v___x_1779_ = l_Lean_SourceInfo_fromRef(v_ref_1750_, v___x_1747_);
v___x_1780_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1781_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1782_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1783_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1784_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1742_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
v_val_1785_ = lean_ctor_get(v___y_1742_, 0);
lean_inc(v_val_1785_);
lean_dec_ref(v___y_1742_);
v___x_1786_ = l_Array_mkArray1___redArg(v_val_1785_);
lean_inc(v_currMacroScope_1749_);
lean_inc(v_quotContext_1748_);
v___y_1471_ = v___x_1757_;
v___y_1472_ = v___x_1782_;
v___y_1473_ = v_a_1771_;
v___y_1474_ = v___x_1784_;
v___y_1475_ = v___x_1765_;
v___y_1476_ = v___x_1765_;
v___y_1477_ = v___x_1778_;
v___y_1478_ = v___x_1780_;
v___y_1479_ = v___x_1781_;
v___y_1480_ = v___x_1783_;
v___y_1481_ = v_quotContext_1748_;
v___y_1482_ = v___x_1768_;
v___y_1483_ = v_currMacroScope_1749_;
v___y_1484_ = v___x_1779_;
v___y_1485_ = v___x_1786_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1787_; 
lean_dec(v___y_1742_);
v___x_1787_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_currMacroScope_1749_);
lean_inc(v_quotContext_1748_);
v___y_1471_ = v___x_1757_;
v___y_1472_ = v___x_1782_;
v___y_1473_ = v_a_1771_;
v___y_1474_ = v___x_1784_;
v___y_1475_ = v___x_1765_;
v___y_1476_ = v___x_1765_;
v___y_1477_ = v___x_1778_;
v___y_1478_ = v___x_1780_;
v___y_1479_ = v___x_1781_;
v___y_1480_ = v___x_1783_;
v___y_1481_ = v_quotContext_1748_;
v___y_1482_ = v___x_1768_;
v___y_1483_ = v_currMacroScope_1749_;
v___y_1484_ = v___x_1779_;
v___y_1485_ = v___x_1787_;
goto v___jp_1470_;
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1792_; lean_object* v_currMacroScope_1793_; lean_object* v_ref_1794_; lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1835_; 
v_quotContext_1792_ = lean_ctor_get(v_a_1286_, 1);
v_currMacroScope_1793_ = lean_ctor_get(v_a_1286_, 2);
v_ref_1794_ = lean_ctor_get(v_a_1286_, 5);
v___x_1795_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1794_, v_a_1286_, v_a_1287_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_a_1797_ = lean_ctor_get(v___x_1795_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1799_ = v___x_1795_;
v_isShared_1800_ = v_isSharedCheck_1835_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1835_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1801_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1802_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1803_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1796_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 2);
lean_ctor_set(v___x_1799_, 1, v___x_1803_);
v___x_1805_ = v___x_1799_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1796_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1833_; 
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59);
v___x_1807_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60));
lean_inc(v_currMacroScope_1793_);
lean_inc(v_quotContext_1792_);
v___x_1808_ = l_Lean_addMacroScope(v_quotContext_1792_, v___x_1807_, v_currMacroScope_1793_);
v___x_1809_ = lean_box(0);
v___x_1810_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63));
lean_inc(v_a_1796_);
v___x_1811_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1796_);
lean_ctor_set(v___x_1811_, 1, v___x_1806_);
lean_ctor_set(v___x_1811_, 2, v___x_1808_);
lean_ctor_set(v___x_1811_, 3, v___x_1810_);
lean_inc_ref(v___x_1805_);
v___x_1812_ = l_Lean_Syntax_node3(v_a_1796_, v___x_1802_, v___x_1805_, v___x_1805_, v___x_1811_);
v___x_1813_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1794_, v_a_1286_, v_a_1797_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_a_1815_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1817_ = v___x_1813_;
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64));
lean_inc(v_a_1814_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 2);
lean_ctor_set(v___x_1817_, 1, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1814_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1822_ = l_Lean_Syntax_node1(v_a_1814_, v___x_1318_, v___x_1821_);
v___x_1823_ = l_Lean_SourceInfo_fromRef(v_ref_1794_, v___x_1743_);
v___x_1824_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1825_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1826_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1827_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1828_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1742_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; 
v_val_1829_ = lean_ctor_get(v___y_1742_, 0);
lean_inc(v_val_1829_);
lean_dec_ref(v___y_1742_);
v___x_1830_ = l_Array_mkArray1___redArg(v_val_1829_);
lean_inc(v_currMacroScope_1793_);
lean_inc(v_quotContext_1792_);
v___y_1612_ = v___x_1827_;
v___y_1613_ = v___x_1826_;
v___y_1614_ = v___x_1824_;
v___y_1615_ = v___x_1809_;
v___y_1616_ = v___x_1812_;
v___y_1617_ = v_quotContext_1792_;
v___y_1618_ = v_currMacroScope_1793_;
v___y_1619_ = v___x_1828_;
v___y_1620_ = v_a_1815_;
v___y_1621_ = v___x_1822_;
v___y_1622_ = v___x_1801_;
v___y_1623_ = v___x_1825_;
v___y_1624_ = v___x_1823_;
v___y_1625_ = v___x_1809_;
v___y_1626_ = v___x_1830_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1831_; 
lean_dec(v___y_1742_);
v___x_1831_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_currMacroScope_1793_);
lean_inc(v_quotContext_1792_);
v___y_1612_ = v___x_1827_;
v___y_1613_ = v___x_1826_;
v___y_1614_ = v___x_1824_;
v___y_1615_ = v___x_1809_;
v___y_1616_ = v___x_1812_;
v___y_1617_ = v_quotContext_1792_;
v___y_1618_ = v_currMacroScope_1793_;
v___y_1619_ = v___x_1828_;
v___y_1620_ = v_a_1815_;
v___y_1621_ = v___x_1822_;
v___y_1622_ = v___x_1801_;
v___y_1623_ = v___x_1825_;
v___y_1624_ = v___x_1823_;
v___y_1625_ = v___x_1809_;
v___y_1626_ = v___x_1831_;
goto v___jp_1611_;
}
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1836_; lean_object* v_currMacroScope_1837_; lean_object* v_ref_1838_; lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v___x_1309_);
v_quotContext_1836_ = lean_ctor_get(v_a_1286_, 1);
v_currMacroScope_1837_ = lean_ctor_get(v_a_1286_, 2);
v_ref_1838_ = lean_ctor_get(v_a_1286_, 5);
v___x_1839_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1838_, v_a_1286_, v_a_1287_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_a_1841_ = lean_ctor_get(v___x_1839_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1843_ = v___x_1839_;
v_isShared_1844_ = v_isSharedCheck_1880_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1880_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1845_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1846_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1847_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1840_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 2);
lean_ctor_set(v___x_1843_, 1, v___x_1847_);
v___x_1849_ = v___x_1843_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1840_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1878_; 
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66);
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67));
lean_inc(v_currMacroScope_1837_);
lean_inc(v_quotContext_1836_);
v___x_1852_ = l_Lean_addMacroScope(v_quotContext_1836_, v___x_1851_, v_currMacroScope_1837_);
v___x_1853_ = lean_box(0);
v___x_1854_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70));
lean_inc(v_a_1840_);
v___x_1855_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1855_, 0, v_a_1840_);
lean_ctor_set(v___x_1855_, 1, v___x_1850_);
lean_ctor_set(v___x_1855_, 2, v___x_1852_);
lean_ctor_set(v___x_1855_, 3, v___x_1854_);
lean_inc_ref(v___x_1849_);
v___x_1856_ = l_Lean_Syntax_node3(v_a_1840_, v___x_1846_, v___x_1849_, v___x_1849_, v___x_1855_);
v___x_1857_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1838_, v_a_1286_, v_a_1841_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_a_1859_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1878_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1878_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71));
lean_inc(v_a_1858_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 2);
lean_ctor_set(v___x_1861_, 1, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1858_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1866_ = l_Lean_Syntax_node1(v_a_1858_, v___x_1318_, v___x_1865_);
v___x_1867_ = 0;
v___x_1868_ = l_Lean_SourceInfo_fromRef(v_ref_1838_, v___x_1867_);
v___x_1869_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1870_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1871_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1872_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1873_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1742_) == 1)
{
lean_object* v_val_1874_; lean_object* v___x_1875_; 
v_val_1874_ = lean_ctor_get(v___y_1742_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v___y_1742_);
v___x_1875_ = l_Array_mkArray1___redArg(v_val_1874_);
lean_inc(v_quotContext_1836_);
lean_inc(v_currMacroScope_1837_);
v___y_1321_ = v___x_1868_;
v___y_1322_ = v_a_1859_;
v___y_1323_ = v___x_1866_;
v___y_1324_ = v___x_1856_;
v___y_1325_ = v___x_1872_;
v___y_1326_ = v___x_1871_;
v___y_1327_ = v_currMacroScope_1837_;
v___y_1328_ = v___x_1853_;
v___y_1329_ = v___x_1873_;
v___y_1330_ = v_quotContext_1836_;
v___y_1331_ = v___x_1853_;
v___y_1332_ = v___x_1870_;
v___y_1333_ = v___x_1845_;
v___y_1334_ = v___x_1869_;
v___y_1335_ = v___x_1875_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1876_; 
lean_dec(v___y_1742_);
v___x_1876_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1836_);
lean_inc(v_currMacroScope_1837_);
v___y_1321_ = v___x_1868_;
v___y_1322_ = v_a_1859_;
v___y_1323_ = v___x_1866_;
v___y_1324_ = v___x_1856_;
v___y_1325_ = v___x_1872_;
v___y_1326_ = v___x_1871_;
v___y_1327_ = v_currMacroScope_1837_;
v___y_1328_ = v___x_1853_;
v___y_1329_ = v___x_1873_;
v___y_1330_ = v_quotContext_1836_;
v___y_1331_ = v___x_1853_;
v___y_1332_ = v___x_1870_;
v___y_1333_ = v___x_1845_;
v___y_1334_ = v___x_1869_;
v___y_1335_ = v___x_1876_;
goto v___jp_1320_;
}
}
}
}
}
}
}
}
v___jp_1288_:
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1290_ = lean_ctor_get(v___y_1289_, 0);
v_a_1291_ = lean_ctor_get(v___y_1289_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1289_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_inc(v_a_1290_);
lean_dec(v___y_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1901_ = l_Lean_Parser_Tactic_optConfig;
v___x_1902_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__3));
v___x_1903_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1904_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1902_);
lean_ctor_set(v___x_1904_, 2, v___x_1901_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_Parser_Tactic_discharger;
v___x_1906_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_1909_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4);
v___x_1910_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1911_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1909_);
lean_ctor_set(v___x_1911_, 2, v___x_1908_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1919_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_1920_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6);
v___x_1921_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1922_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1920_);
lean_ctor_set(v___x_1922_, 2, v___x_1919_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1926_ = l_Lean_Parser_Tactic_simpLemma;
v___x_1927_ = l_Lean_Parser_Tactic_simpErase;
v___x_1928_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_1929_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1927_);
lean_ctor_set(v___x_1929_, 2, v___x_1926_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1930_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_1931_ = l_Lean_Parser_Tactic_simpStar;
v___x_1932_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_1933_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___x_1931_);
lean_ctor_set(v___x_1933_, 2, v___x_1930_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18(void){
_start:
{
uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1938_ = 0;
v___x_1939_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_1940_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_1941_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__14, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14);
v___x_1942_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
lean_ctor_set(v___x_1942_, 2, v___x_1939_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*3, v___x_1938_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1943_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__18, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18);
v___x_1944_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_1945_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1946_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1944_);
lean_ctor_set(v___x_1946_, 2, v___x_1943_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1949_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_1950_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__19, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19);
v___x_1951_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1952_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1950_);
lean_ctor_set(v___x_1952_, 2, v___x_1949_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__21, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21);
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1956_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_1957_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10);
v___x_1958_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1959_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___x_1957_);
lean_ctor_set(v___x_1959_, 2, v___x_1956_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1960_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_1961_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__23, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23);
v___x_1962_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1963_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1961_);
lean_ctor_set(v___x_1963_, 2, v___x_1960_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1964_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__24, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24);
v___x_1965_ = lean_unsigned_to_nat(1022u);
v___x_1966_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1));
v___x_1967_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v___x_1965_);
lean_ctor_set(v___x_1967_, 2, v___x_1964_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold(void){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__25, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
v___x_1971_ = l_String_toRawSubstring_x27(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(lean_object* v_s_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_quotContext_1977_; lean_object* v_currMacroScope_1978_; lean_object* v_ref_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_quotContext_1977_ = lean_ctor_get(v_a_1975_, 1);
lean_inc(v_quotContext_1977_);
v_currMacroScope_1978_ = lean_ctor_get(v_a_1975_, 2);
lean_inc(v_currMacroScope_1978_);
v_ref_1979_ = lean_ctor_get(v_a_1975_, 5);
lean_inc(v_ref_1979_);
lean_dec_ref(v_a_1975_);
v___x_1980_ = 0;
v___x_1981_ = l_Lean_SourceInfo_fromRef(v_ref_1979_, v___x_1980_);
lean_dec(v_ref_1979_);
v___x_1982_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_1983_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1984_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_1985_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_1986_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___x_1981_);
v___x_1987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1981_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_1989_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc(v_currMacroScope_1978_);
lean_inc(v_quotContext_1977_);
v___x_1990_ = l_Lean_addMacroScope(v_quotContext_1977_, v___x_1989_, v_currMacroScope_1978_);
v___x_1991_ = lean_box(0);
lean_inc(v___x_1981_);
v___x_1992_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1981_);
lean_ctor_set(v___x_1992_, 1, v___x_1988_);
lean_ctor_set(v___x_1992_, 2, v___x_1990_);
lean_ctor_set(v___x_1992_, 3, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___x_1981_);
v___x_1994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1981_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76);
v___x_1996_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77));
v___x_1997_ = l_Lean_addMacroScope(v_quotContext_1977_, v___x_1996_, v_currMacroScope_1978_);
v___x_1998_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81));
lean_inc(v___x_1981_);
v___x_1999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1981_);
lean_ctor_set(v___x_1999_, 1, v___x_1995_);
lean_ctor_set(v___x_1999_, 2, v___x_1997_);
lean_ctor_set(v___x_1999_, 3, v___x_1998_);
v___x_2000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___x_1981_);
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1981_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
lean_inc(v___x_1981_);
v___x_2002_ = l_Lean_Syntax_node5(v___x_1981_, v___x_1985_, v___x_1987_, v___x_1992_, v___x_1994_, v___x_1999_, v___x_2001_);
lean_inc(v___x_1981_);
v___x_2003_ = l_Lean_Syntax_node1(v___x_1981_, v___x_1984_, v___x_2002_);
lean_inc(v___x_1981_);
v___x_2004_ = l_Lean_Syntax_node1(v___x_1981_, v___x_1983_, v___x_2003_);
v___x_2005_ = l_Lean_Syntax_node1(v___x_1981_, v___x_1982_, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_2007_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68));
v___x_2008_ = l_Lean_Syntax_setKind(v_s_1974_, v___x_2007_);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l_Lean_Syntax_getArg(v___x_2008_, v___x_2009_);
v___x_2011_ = 1;
v___x_2012_ = l_Lean_mkAtomFrom(v___x_2010_, v___x_2006_, v___x_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = l_Lean_Syntax_setArg(v___x_2008_, v___x_2009_, v___x_2012_);
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = l_Lean_Syntax_getArg(v___x_2013_, v___x_2014_);
v___x_2016_ = l_Lean_Parser_Tactic_appendConfig(v___x_2015_, v___x_2005_);
v___x_2017_ = l_Lean_Syntax_setArg(v___x_2013_, v___x_2014_, v___x_2016_);
v___x_2018_ = l_Lean_Syntax_mkSynthetic(v___x_2017_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v_a_1976_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__4(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = l_Lean_Parser_Tactic_optConfig;
v___x_2031_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__3));
v___x_2032_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2033_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_2031_);
lean_ctor_set(v___x_2033_, 2, v___x_2030_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__5(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2035_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__4, &l_Lean_Parser_Tactic_simpArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpArith___closed__4);
v___x_2036_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2037_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v___x_2035_);
lean_ctor_set(v___x_2037_, 2, v___x_2034_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__6(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2039_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__5, &l_Lean_Parser_Tactic_simpArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpArith___closed__5);
v___x_2040_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2041_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
lean_ctor_set(v___x_2041_, 2, v___x_2038_);
return v___x_2041_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__7(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2043_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__6, &l_Lean_Parser_Tactic_simpArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpArith___closed__6);
v___x_2044_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2045_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___x_2043_);
lean_ctor_set(v___x_2045_, 2, v___x_2042_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__8(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2047_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__7, &l_Lean_Parser_Tactic_simpArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpArith___closed__7);
v___x_2048_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2049_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
lean_ctor_set(v___x_2049_, 2, v___x_2046_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__9(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__8, &l_Lean_Parser_Tactic_simpArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpArith___closed__8);
v___x_2051_ = lean_unsigned_to_nat(1022u);
v___x_2052_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__1));
v___x_2053_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2051_);
lean_ctor_set(v___x_2053_, 2, v___x_2050_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith(void){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__9, &l_Lean_Parser_Tactic_simpArith___closed__9_once, _init_l_Lean_Parser_Tactic_simpArith___closed__9);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__4(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = l_Lean_Parser_Tactic_optConfig;
v___x_2066_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__3));
v___x_2067_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2068_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2066_);
lean_ctor_set(v___x_2068_, 2, v___x_2065_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__5(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2070_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__4, &l_Lean_Parser_Tactic_simpArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__4);
v___x_2071_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2072_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2070_);
lean_ctor_set(v___x_2072_, 2, v___x_2069_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__6(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2074_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__5, &l_Lean_Parser_Tactic_simpArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__5);
v___x_2075_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2076_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
lean_ctor_set(v___x_2076_, 2, v___x_2073_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__7(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2078_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__6, &l_Lean_Parser_Tactic_simpArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__6);
v___x_2079_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2080_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
lean_ctor_set(v___x_2080_, 2, v___x_2077_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__8(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2082_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__7, &l_Lean_Parser_Tactic_simpArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__7);
v___x_2083_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2084_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2081_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__9(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__8, &l_Lean_Parser_Tactic_simpArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__8);
v___x_2086_ = lean_unsigned_to_nat(1022u);
v___x_2087_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__1));
v___x_2088_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___x_2085_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang(void){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__9, &l_Lean_Parser_Tactic_simpArithBang___closed__9_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__9);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2100_ = l_Lean_Parser_Tactic_optConfig;
v___x_2101_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3));
v___x_2102_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2103_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2100_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2104_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2105_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4);
v___x_2106_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2107_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2105_);
lean_ctor_set(v___x_2107_, 2, v___x_2104_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2108_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2109_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5);
v___x_2110_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2111_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2109_);
lean_ctor_set(v___x_2111_, 2, v___x_2108_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7(void){
_start:
{
uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2112_ = 0;
v___x_2113_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_2114_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_2115_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_2116_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2114_);
lean_ctor_set(v___x_2116_, 2, v___x_2113_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*3, v___x_2112_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7);
v___x_2118_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_2119_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2120_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2118_);
lean_ctor_set(v___x_2120_, 2, v___x_2117_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_2122_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8);
v___x_2123_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2124_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2121_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9);
v___x_2126_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2129_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6);
v___x_2130_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2131_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2128_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11);
v___x_2133_ = lean_unsigned_to_nat(1022u);
v___x_2134_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1));
v___x_2135_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
lean_ctor_set(v___x_2135_, 1, v___x_2133_);
lean_ctor_set(v___x_2135_, 2, v___x_2132_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold(void){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(lean_object* v_s_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_quotContext_2141_; lean_object* v_currMacroScope_2142_; lean_object* v_ref_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_quotContext_2141_ = lean_ctor_get(v_a_2139_, 1);
lean_inc(v_quotContext_2141_);
v_currMacroScope_2142_ = lean_ctor_get(v_a_2139_, 2);
lean_inc(v_currMacroScope_2142_);
v_ref_2143_ = lean_ctor_get(v_a_2139_, 5);
lean_inc(v_ref_2143_);
lean_dec_ref(v_a_2139_);
v___x_2144_ = 0;
v___x_2145_ = l_Lean_SourceInfo_fromRef(v_ref_2143_, v___x_2144_);
lean_dec(v_ref_2143_);
v___x_2146_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2147_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2148_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2149_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2150_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___x_2145_);
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2145_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2153_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc(v_currMacroScope_2142_);
lean_inc(v_quotContext_2141_);
v___x_2154_ = l_Lean_addMacroScope(v_quotContext_2141_, v___x_2153_, v_currMacroScope_2142_);
v___x_2155_ = lean_box(0);
lean_inc(v___x_2145_);
v___x_2156_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2145_);
lean_ctor_set(v___x_2156_, 1, v___x_2152_);
lean_ctor_set(v___x_2156_, 2, v___x_2154_);
lean_ctor_set(v___x_2156_, 3, v___x_2155_);
v___x_2157_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___x_2145_);
v___x_2158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2145_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76);
v___x_2160_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77));
v___x_2161_ = l_Lean_addMacroScope(v_quotContext_2141_, v___x_2160_, v_currMacroScope_2142_);
v___x_2162_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81));
lean_inc(v___x_2145_);
v___x_2163_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2145_);
lean_ctor_set(v___x_2163_, 1, v___x_2159_);
lean_ctor_set(v___x_2163_, 2, v___x_2161_);
lean_ctor_set(v___x_2163_, 3, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___x_2145_);
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2145_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v___x_2145_);
v___x_2166_ = l_Lean_Syntax_node5(v___x_2145_, v___x_2149_, v___x_2151_, v___x_2156_, v___x_2158_, v___x_2163_, v___x_2165_);
lean_inc(v___x_2145_);
v___x_2167_ = l_Lean_Syntax_node1(v___x_2145_, v___x_2148_, v___x_2166_);
lean_inc(v___x_2145_);
v___x_2168_ = l_Lean_Syntax_node1(v___x_2145_, v___x_2147_, v___x_2167_);
v___x_2169_ = l_Lean_Syntax_node1(v___x_2145_, v___x_2146_, v___x_2168_);
v___x_2170_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61));
v___x_2171_ = l_Lean_Syntax_setKind(v_s_2138_, v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2172_);
v___x_2174_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_));
v___x_2175_ = 1;
v___x_2176_ = l_Lean_mkAtomFrom(v___x_2173_, v___x_2174_, v___x_2175_);
lean_dec(v___x_2173_);
v___x_2177_ = l_Lean_Syntax_setArg(v___x_2171_, v___x_2172_, v___x_2176_);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = l_Lean_Syntax_getArg(v___x_2177_, v___x_2178_);
v___x_2180_ = l_Lean_Parser_Tactic_appendConfig(v___x_2179_, v___x_2169_);
v___x_2181_ = l_Lean_Syntax_setArg(v___x_2177_, v___x_2178_, v___x_2180_);
v___x_2182_ = l_Lean_Syntax_mkSynthetic(v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v_a_2140_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__4(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = l_Lean_Parser_Tactic_optConfig;
v___x_2195_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__3));
v___x_2196_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2197_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
lean_ctor_set(v___x_2197_, 2, v___x_2194_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__5(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2199_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__4, &l_Lean_Parser_Tactic_simpAllArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__4);
v___x_2200_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2201_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__6(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2203_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__5, &l_Lean_Parser_Tactic_simpAllArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__5);
v___x_2204_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2205_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
lean_ctor_set(v___x_2205_, 2, v___x_2202_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__7(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2207_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__6, &l_Lean_Parser_Tactic_simpAllArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__6);
v___x_2208_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2209_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__8(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__7, &l_Lean_Parser_Tactic_simpAllArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__7);
v___x_2211_ = lean_unsigned_to_nat(1022u);
v___x_2212_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__1));
v___x_2213_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2210_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith(void){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__8, &l_Lean_Parser_Tactic_simpAllArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__8);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = l_Lean_Parser_Tactic_optConfig;
v___x_2226_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__3));
v___x_2227_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2228_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
lean_ctor_set(v___x_2228_, 2, v___x_2225_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2230_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__4, &l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4);
v___x_2231_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2232_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v___x_2229_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2234_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__5, &l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5);
v___x_2235_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2236_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___x_2234_);
lean_ctor_set(v___x_2236_, 2, v___x_2233_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2238_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__6, &l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6);
v___x_2239_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2240_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set(v___x_2240_, 2, v___x_2237_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__7, &l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7);
v___x_2242_ = lean_unsigned_to_nat(1022u);
v___x_2243_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__1));
v___x_2244_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
lean_ctor_set(v___x_2244_, 2, v___x_2241_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang(void){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__8, &l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8);
return v___x_2245_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = l_Lean_Parser_Tactic_optConfig;
v___x_2257_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3));
v___x_2258_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2259_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
lean_ctor_set(v___x_2259_, 2, v___x_2256_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2261_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4);
v___x_2262_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2263_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2261_);
lean_ctor_set(v___x_2263_, 2, v___x_2260_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2265_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5);
v___x_2266_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2267_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2265_);
lean_ctor_set(v___x_2267_, 2, v___x_2264_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2269_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6);
v___x_2270_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2271_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2269_);
lean_ctor_set(v___x_2271_, 2, v___x_2268_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2272_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2273_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7);
v___x_2274_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2275_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2273_);
lean_ctor_set(v___x_2275_, 2, v___x_2272_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8);
v___x_2277_ = lean_unsigned_to_nat(1022u);
v___x_2278_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1));
v___x_2279_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
lean_ctor_set(v___x_2279_, 2, v___x_2276_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold(void){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(lean_object* v_s_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_quotContext_2284_; lean_object* v_currMacroScope_2285_; lean_object* v_ref_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_quotContext_2284_ = lean_ctor_get(v_a_2282_, 1);
lean_inc(v_quotContext_2284_);
v_currMacroScope_2285_ = lean_ctor_get(v_a_2282_, 2);
lean_inc(v_currMacroScope_2285_);
v_ref_2286_ = lean_ctor_get(v_a_2282_, 5);
lean_inc(v_ref_2286_);
lean_dec_ref(v_a_2282_);
v___x_2287_ = 0;
v___x_2288_ = l_Lean_SourceInfo_fromRef(v_ref_2286_, v___x_2287_);
lean_dec(v_ref_2286_);
v___x_2289_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2290_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2291_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2292_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2293_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc(v___x_2288_);
v___x_2294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2288_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2296_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc(v_currMacroScope_2285_);
lean_inc(v_quotContext_2284_);
v___x_2297_ = l_Lean_addMacroScope(v_quotContext_2284_, v___x_2296_, v_currMacroScope_2285_);
v___x_2298_ = lean_box(0);
lean_inc(v___x_2288_);
v___x_2299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2288_);
lean_ctor_set(v___x_2299_, 1, v___x_2295_);
lean_ctor_set(v___x_2299_, 2, v___x_2297_);
lean_ctor_set(v___x_2299_, 3, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
lean_inc(v___x_2288_);
v___x_2301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2288_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76);
v___x_2303_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77));
v___x_2304_ = l_Lean_addMacroScope(v_quotContext_2284_, v___x_2303_, v_currMacroScope_2285_);
v___x_2305_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81));
lean_inc(v___x_2288_);
v___x_2306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2288_);
lean_ctor_set(v___x_2306_, 1, v___x_2302_);
lean_ctor_set(v___x_2306_, 2, v___x_2304_);
lean_ctor_set(v___x_2306_, 3, v___x_2305_);
v___x_2307_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
lean_inc(v___x_2288_);
v___x_2308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2288_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
lean_inc(v___x_2288_);
v___x_2309_ = l_Lean_Syntax_node5(v___x_2288_, v___x_2292_, v___x_2294_, v___x_2299_, v___x_2301_, v___x_2306_, v___x_2308_);
lean_inc(v___x_2288_);
v___x_2310_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2291_, v___x_2309_);
lean_inc(v___x_2288_);
v___x_2311_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2290_, v___x_2310_);
v___x_2312_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2289_, v___x_2311_);
v___x_2313_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_2314_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52));
v___x_2315_ = l_Lean_Syntax_setKind(v_s_2281_, v___x_2314_);
v___x_2316_ = lean_unsigned_to_nat(0u);
v___x_2317_ = l_Lean_Syntax_getArg(v___x_2315_, v___x_2316_);
v___x_2318_ = 1;
v___x_2319_ = l_Lean_mkAtomFrom(v___x_2317_, v___x_2313_, v___x_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = l_Lean_Syntax_setArg(v___x_2315_, v___x_2316_, v___x_2319_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = l_Lean_Syntax_getArg(v___x_2320_, v___x_2321_);
v___x_2323_ = l_Lean_Parser_Tactic_appendConfig(v___x_2322_, v___x_2312_);
v___x_2324_ = l_Lean_Syntax_setArg(v___x_2320_, v___x_2321_, v___x_2323_);
v___x_2325_ = l_Lean_Syntax_mkSynthetic(v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2283_);
return v___x_2326_;
}
}
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticErw______ = _init_l_Lean_Parser_Tactic_tacticErw______();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticErw______);
l_Lean_Parser_Tactic_declareSimpLikeTactic = _init_l_Lean_Parser_Tactic_declareSimpLikeTactic();
lean_mark_persistent(l_Lean_Parser_Tactic_declareSimpLikeTactic);
l_Lean_Parser_Tactic_simpAutoUnfold = _init_l_Lean_Parser_Tactic_simpAutoUnfold();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAutoUnfold);
l_Lean_Parser_Tactic_simpArith = _init_l_Lean_Parser_Tactic_simpArith();
lean_mark_persistent(l_Lean_Parser_Tactic_simpArith);
l_Lean_Parser_Tactic_simpArithBang = _init_l_Lean_Parser_Tactic_simpArithBang();
lean_mark_persistent(l_Lean_Parser_Tactic_simpArithBang);
l_Lean_Parser_Tactic_simpAllAutoUnfold = _init_l_Lean_Parser_Tactic_simpAllAutoUnfold();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAllAutoUnfold);
l_Lean_Parser_Tactic_simpAllArith = _init_l_Lean_Parser_Tactic_simpAllArith();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAllArith);
l_Lean_Parser_Tactic_simpAllArithBang = _init_l_Lean_Parser_Tactic_simpAllArithBang();
lean_mark_persistent(l_Lean_Parser_Tactic_simpAllArithBang);
l_Lean_Parser_Tactic_dsimpAutoUnfold = _init_l_Lean_Parser_Tactic_dsimpAutoUnfold();
lean_mark_persistent(l_Lean_Parser_Tactic_dsimpAutoUnfold);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
