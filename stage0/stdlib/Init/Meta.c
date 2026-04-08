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
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrec"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 162, 64, 41, 156, 201, 248, 85)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addPrio"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 218, 70, 150, 87, 9, 79, 160)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrio"};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 12, 102, 115, 130, 88, 1, 102)}};
static const lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "s.setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value),LEAN_SCALAR_PTR_LITERAL(10, 5, 190, 174, 53, 198, 104, 96)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "s.setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value),LEAN_SCALAR_PTR_LITERAL(51, 18, 73, 41, 18, 128, 68, 244)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkAtomFrom"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value),LEAN_SCALAR_PTR_LITERAL(92, 136, 63, 126, 134, 85, 56, 129)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 207, 191, 201, 123, 75, 165)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "appendConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value),LEAN_SCALAR_PTR_LITERAL(211, 122, 231, 137, 224, 73, 76, 35)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "s.mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value),LEAN_SCALAR_PTR_LITERAL(32, 59, 47, 97, 193, 185, 105, 5)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___boxed(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1(v_x_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1));
lean_inc(v_x_66_);
v___x_70_ = l_Lean_Syntax_isOfKind(v_x_66_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_x_66_);
v___x_71_ = lean_box(1);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_a_68_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Lean_Syntax_getArg(v_x_66_, v___x_73_);
v___x_75_ = l_Lean_evalPrec(v___x_74_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
v_a_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_a_77_);
lean_dec_ref(v___x_75_);
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = l_Lean_Syntax_getArg(v_x_66_, v___x_78_);
lean_dec(v_x_66_);
v___x_80_ = l_Lean_evalPrec(v___x_79_, v_a_67_, v_a_77_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_93_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_a_82_ = lean_ctor_get(v___x_80_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_93_ == 0)
{
v___x_84_ = v___x_80_;
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_86_ = lean_nat_sub(v_a_76_, v_a_81_);
lean_dec(v_a_81_);
lean_dec(v_a_76_);
v___x_87_ = l_Nat_reprFast(v___x_86_);
v___x_88_ = lean_box(2);
v___x_89_ = l_Lean_Syntax_mkNumLit(v___x_87_, v___x_88_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_89_);
v___x_91_ = v___x_84_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_a_82_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v_a_76_);
v_a_94_ = lean_ctor_get(v___x_80_, 0);
v_a_95_ = lean_ctor_get(v___x_80_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_80_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_inc(v_a_94_);
lean_dec(v___x_80_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_x_66_);
v_a_103_ = lean_ctor_get(v___x_75_, 0);
v_a_104_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_75_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_75_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_103_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___boxed(lean_object* v_x_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(v_x_112_, v_a_113_, v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(lean_object* v_x_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__1));
lean_inc(v_x_141_);
v___x_145_ = l_Lean_Syntax_isOfKind(v_x_141_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_x_141_);
v___x_146_ = lean_box(1);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_143_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = l_Lean_Syntax_getArg(v_x_141_, v___x_148_);
lean_dec(v_x_141_);
v___x_150_ = l_Lean_evalPrec(v___x_149_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_162_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_a_152_ = lean_ctor_get(v___x_150_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_162_ == 0)
{
v___x_154_ = v___x_150_;
v_isShared_155_ = v_isSharedCheck_162_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_162_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_156_ = l_Nat_reprFast(v_a_151_);
v___x_157_ = lean_box(2);
v___x_158_ = l_Lean_Syntax_mkNumLit(v___x_156_, v___x_157_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_158_);
v___x_160_ = v___x_154_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_a_152_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_163_ = lean_ctor_get(v___x_150_, 0);
v_a_164_ = lean_ctor_get(v___x_150_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_150_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_inc(v_a_163_);
lean_dec(v___x_150_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1___boxed(lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(v_x_172_, v_a_173_, v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1));
lean_inc(v_x_182_);
v___x_186_ = l_Lean_Syntax_isOfKind(v_x_182_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_x_182_);
v___x_187_ = lean_box(1);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l_Lean_Syntax_getArg(v_x_182_, v___x_189_);
v___x_191_ = l_Lean_evalPrio(v___x_190_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
v_a_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_a_193_);
lean_dec_ref(v___x_191_);
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = l_Lean_Syntax_getArg(v_x_182_, v___x_194_);
lean_dec(v_x_182_);
v___x_196_ = l_Lean_evalPrio(v___x_195_, v_a_183_, v_a_193_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_209_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_a_198_ = lean_ctor_get(v___x_196_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_209_ == 0)
{
v___x_200_ = v___x_196_;
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_202_ = lean_nat_add(v_a_192_, v_a_197_);
lean_dec(v_a_197_);
lean_dec(v_a_192_);
v___x_203_ = l_Nat_reprFast(v___x_202_);
v___x_204_ = lean_box(2);
v___x_205_ = l_Lean_Syntax_mkNumLit(v___x_203_, v___x_204_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_205_);
v___x_207_ = v___x_200_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_a_198_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_a_192_);
v_a_210_ = lean_ctor_get(v___x_196_, 0);
v_a_211_ = lean_ctor_get(v___x_196_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_196_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_inc(v_a_210_);
lean_dec(v___x_196_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_210_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_x_182_);
v_a_219_ = lean_ctor_get(v___x_191_, 0);
v_a_220_ = lean_ctor_get(v___x_191_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_191_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_inc(v_a_219_);
lean_dec(v___x_191_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_219_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(v_x_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(lean_object* v_x_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1));
lean_inc(v_x_238_);
v___x_242_ = l_Lean_Syntax_isOfKind(v_x_238_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_x_238_);
v___x_243_ = lean_box(1);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_a_240_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Syntax_getArg(v_x_238_, v___x_245_);
v___x_247_ = l_Lean_evalPrio(v___x_246_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
v_a_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_a_249_);
lean_dec_ref(v___x_247_);
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = l_Lean_Syntax_getArg(v_x_238_, v___x_250_);
lean_dec(v_x_238_);
v___x_252_ = l_Lean_evalPrio(v___x_251_, v_a_239_, v_a_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_265_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_256_ = v___x_252_;
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_258_ = lean_nat_sub(v_a_248_, v_a_253_);
lean_dec(v_a_253_);
lean_dec(v_a_248_);
v___x_259_ = l_Nat_reprFast(v___x_258_);
v___x_260_ = lean_box(2);
v___x_261_ = l_Lean_Syntax_mkNumLit(v___x_259_, v___x_260_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_261_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_a_254_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_a_248_);
v_a_266_ = lean_ctor_get(v___x_252_, 0);
v_a_267_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_252_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_inc(v_a_266_);
lean_dec(v___x_252_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_266_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_x_238_);
v_a_275_ = lean_ctor_get(v___x_247_, 0);
v_a_276_ = lean_ctor_get(v___x_247_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_247_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_inc(v_a_275_);
lean_dec(v___x_247_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_275_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___boxed(lean_object* v_x_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(v_x_284_, v_a_285_, v_a_286_);
lean_dec_ref(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_termEval__prio___00__closed__1));
lean_inc(v_x_310_);
v___x_314_ = l_Lean_Syntax_isOfKind(v_x_310_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_x_310_);
v___x_315_ = lean_box(1);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = l_Lean_Syntax_getArg(v_x_310_, v___x_317_);
lean_dec(v_x_310_);
v___x_319_ = l_Lean_evalPrio(v___x_318_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_a_321_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_331_ == 0)
{
v___x_323_ = v___x_319_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_325_ = l_Nat_reprFast(v_a_320_);
v___x_326_ = lean_box(2);
v___x_327_ = l_Lean_Syntax_mkNumLit(v___x_325_, v___x_326_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_327_);
v___x_329_ = v___x_323_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_321_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_a_332_ = lean_ctor_get(v___x_319_, 0);
v_a_333_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_319_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_inc(v_a_332_);
lean_dec(v___x_319_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_332_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1___boxed(lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(v_x_341_, v_a_342_, v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_356_ = l_Lean_Parser_Tactic_optConfig;
v___x_357_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__4));
v___x_358_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_359_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
lean_ctor_set(v___x_359_, 2, v___x_356_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_361_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__5, &l_Lean_Parser_Tactic_tacticErw_______00__closed__5_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5);
v___x_362_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_363_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_360_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_Parser_Tactic_location;
v___x_368_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_371_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__6, &l_Lean_Parser_Tactic_tacticErw_______00__closed__6_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6);
v___x_372_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_373_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__10, &l_Lean_Parser_Tactic_tacticErw_______00__closed__10_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10);
v___x_375_ = lean_unsigned_to_nat(1022u);
v___x_376_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__2));
v___x_377_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
lean_ctor_set(v___x_377_, 2, v___x_374_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticErw______(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__11, &l_Lean_Parser_Tactic_tacticErw_______00__closed__11_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t v_sz_379_, size_t v_i_380_, lean_object* v_bs_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_380_, v_sz_379_);
if (v___x_382_ == 0)
{
return v_bs_381_;
}
else
{
lean_object* v_v_383_; lean_object* v___x_384_; lean_object* v_bs_x27_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v_v_383_ = lean_array_uget(v_bs_381_, v_i_380_);
v___x_384_ = lean_unsigned_to_nat(0u);
v_bs_x27_385_ = lean_array_uset(v_bs_381_, v_i_380_, v___x_384_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_380_, v___x_386_);
v___x_388_ = lean_array_uset(v_bs_x27_385_, v_i_380_, v_v_383_);
v_i_380_ = v___x_387_;
v_bs_381_ = v___x_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0___boxed(lean_object* v_sz_390_, lean_object* v_i_391_, lean_object* v_bs_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_390_);
lean_dec(v_sz_390_);
v_i_boxed_394_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_boxed_393_, v_i_boxed_394_, v_bs_392_);
return v_res_395_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Array_mkArray0(lean_box(0));
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21));
v___x_442_ = l_String_toRawSubstring_x27(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(lean_object* v_x_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__2));
lean_inc(v_x_463_);
v___x_467_ = l_Lean_Syntax_isOfKind(v_x_463_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_x_463_);
v___x_468_ = lean_box(1);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_465_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_487_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = l_Lean_Syntax_getArg(v_x_463_, v___x_470_);
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = l_Lean_Syntax_getArg(v_x_463_, v___x_472_);
v___x_535_ = lean_unsigned_to_nat(3u);
v___x_536_ = l_Lean_Syntax_getArg(v_x_463_, v___x_535_);
lean_dec(v_x_463_);
v___x_537_ = l_Lean_Syntax_getOptional_x3f(v___x_536_);
lean_dec(v___x_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
v___y_487_ = v___x_538_;
goto v___jp_486_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_val_539_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_val_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v___y_487_ = v___x_544_;
goto v___jp_486_;
}
}
}
v___jp_474_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = l_Array_append___redArg(v___y_477_, v___y_481_);
lean_dec_ref(v___y_481_);
lean_inc(v___y_478_);
lean_inc(v___y_475_);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v___y_475_);
lean_ctor_set(v___x_483_, 1, v___y_478_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_inc(v___y_479_);
v___x_484_ = l_Lean_Syntax_node4(v___y_475_, v___y_479_, v___y_480_, v___y_476_, v___x_473_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_a_465_);
return v___x_485_;
}
v___jp_486_:
{
lean_object* v_quotContext_488_; lean_object* v_currMacroScope_489_; lean_object* v_ref_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; size_t v_sz_500_; size_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_quotContext_488_ = lean_ctor_get(v_a_464_, 1);
v_currMacroScope_489_ = lean_ctor_get(v_a_464_, 2);
v_ref_490_ = lean_ctor_get(v_a_464_, 5);
v___x_491_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_492_ = 0;
v___x_493_ = l_Lean_SourceInfo_fromRef(v_ref_490_, v___x_492_);
v___x_494_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3));
v___x_495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4));
lean_inc_n(v___x_493_, 12);
v___x_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_498_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
v___x_499_ = l_Lean_Parser_Tactic_getConfigItems(v___x_471_);
v_sz_500_ = lean_array_size(v___x_499_);
v___x_501_ = ((size_t)0ULL);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_500_, v___x_501_, v___x_499_);
v___x_503_ = l_Array_append___redArg(v___x_498_, v___x_502_);
lean_dec_ref(v___x_502_);
v___x_504_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_505_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_506_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_493_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14);
v___x_509_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15));
lean_inc_n(v_currMacroScope_489_, 2);
lean_inc_n(v_quotContext_488_, 2);
v___x_510_ = l_Lean_addMacroScope(v_quotContext_488_, v___x_509_, v_currMacroScope_489_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_493_);
lean_ctor_set(v___x_512_, 1, v___x_508_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v___x_511_);
v___x_513_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_493_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19));
v___x_516_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20));
v___x_517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_493_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22);
v___x_519_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23));
v___x_520_ = l_Lean_addMacroScope(v_quotContext_488_, v___x_519_, v_currMacroScope_489_);
v___x_521_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29));
v___x_522_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_522_, 0, v___x_493_);
lean_ctor_set(v___x_522_, 1, v___x_518_);
lean_ctor_set(v___x_522_, 2, v___x_520_);
lean_ctor_set(v___x_522_, 3, v___x_521_);
v___x_523_ = l_Lean_Syntax_node2(v___x_493_, v___x_515_, v___x_517_, v___x_522_);
v___x_524_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_493_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_Syntax_node5(v___x_493_, v___x_505_, v___x_507_, v___x_512_, v___x_514_, v___x_523_, v___x_525_);
v___x_527_ = l_Lean_Syntax_node1(v___x_493_, v___x_504_, v___x_526_);
v___x_528_ = lean_array_push(v___x_503_, v___x_527_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_493_);
lean_ctor_set(v___x_529_, 1, v___x_497_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
v___x_530_ = l_Lean_Syntax_node1(v___x_493_, v___x_491_, v___x_529_);
if (lean_obj_tag(v___y_487_) == 0)
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___y_475_ = v___x_493_;
v___y_476_ = v___x_530_;
v___y_477_ = v___x_498_;
v___y_478_ = v___x_497_;
v___y_479_ = v___x_494_;
v___y_480_ = v___x_496_;
v___y_481_ = v___x_531_;
goto v___jp_474_;
}
else
{
lean_object* v_val_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_val_532_ = lean_ctor_get(v___y_487_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v___y_487_);
v___x_533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___x_534_ = lean_array_push(v___x_533_, v_val_532_);
v___y_475_ = v___x_493_;
v___y_476_ = v___x_530_;
v___y_477_ = v___x_498_;
v___y_478_ = v___x_497_;
v___y_479_ = v___x_494_;
v___y_480_ = v___x_496_;
v___y_481_ = v___x_534_;
goto v___jp_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___boxed(lean_object* v_x_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(v_x_547_, v_a_548_, v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_550_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = l_Lean_Parser_Tactic_optConfig;
v___x_711_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30));
v___x_712_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_713_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
lean_ctor_set(v___x_713_, 2, v___x_710_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31);
v___x_715_ = lean_unsigned_to_nat(1022u);
v___x_716_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
v___x_717_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_714_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(lean_object* v_____do__lift_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = 0;
v___x_723_ = l_Lean_SourceInfo_fromRef(v_____do__lift_719_, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___y_721_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0___boxed(lean_object* v_____do__lift_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_____do__lift_725_, v___y_726_, v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v_____do__lift_725_);
return v_res_728_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14));
v___x_745_ = l_String_toRawSubstring_x27(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20));
v___x_753_ = l_String_toRawSubstring_x27(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26));
v___x_761_ = l_String_toRawSubstring_x27(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37));
v___x_774_ = l_String_toRawSubstring_x27(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50));
v___x_789_ = l_String_toRawSubstring_x27(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54));
v___x_796_ = l_String_toRawSubstring_x27(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65));
v___x_812_ = l_String_toRawSubstring_x27(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67));
v___x_815_ = l_String_toRawSubstring_x27(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74));
v___x_825_ = l_String_toRawSubstring_x27(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__13));
v___x_829_ = l_String_toRawSubstring_x27(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84));
v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87));
v___x_850_ = l_String_toRawSubstring_x27(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_____x_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_snd_870_; lean_object* v_fst_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_1141_; 
v_snd_870_ = lean_ctor_get(v_____x_867_, 1);
v_fst_871_ = lean_ctor_get(v_____x_867_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_____x_867_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_873_ = v_____x_867_;
v_isShared_874_ = v_isSharedCheck_1141_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_870_);
lean_inc(v_fst_871_);
lean_dec(v_____x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_1141_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_1140_; 
v_fst_875_ = lean_ctor_get(v_snd_870_, 0);
v_snd_876_ = lean_ctor_get(v_snd_870_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_snd_870_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_878_ = v_snd_870_;
v_isShared_879_ = v_isSharedCheck_1140_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snd_876_);
lean_inc(v_fst_875_);
lean_dec(v_snd_870_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_1140_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_quotContext_880_; lean_object* v_currMacroScope_881_; lean_object* v_ref_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v_quotContext_880_ = lean_ctor_get(v___y_868_, 1);
v_currMacroScope_881_ = lean_ctor_get(v___y_868_, 2);
v_ref_882_ = lean_ctor_get(v___y_868_, 5);
v___x_883_ = 0;
v___x_884_ = l_Lean_SourceInfo_fromRef(v_ref_882_, v___x_883_);
v___x_885_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_886_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_887_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1));
lean_inc_ref_n(v___x_860_, 3);
lean_inc_ref_n(v___x_859_, 3);
v___x_888_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2));
v___x_890_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_889_);
v___x_891_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
lean_inc_n(v___x_884_, 2);
v___x_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_892_, 0, v___x_884_);
lean_ctor_set(v___x_892_, 1, v___x_885_);
lean_ctor_set(v___x_892_, 2, v___x_891_);
v___x_893_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_894_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3));
v___x_895_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_894_);
v___x_896_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4));
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 2);
lean_ctor_set(v___x_878_, 1, v___x_896_);
lean_ctor_set(v___x_878_, 0, v___x_884_);
v___x_898_ = v___x_878_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_1139_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_899_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5));
lean_inc_ref_n(v___x_860_, 3);
lean_inc_ref_n(v___x_859_, 3);
v___x_900_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
v___x_902_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_901_);
lean_inc_ref(v___x_892_);
lean_inc_n(v___x_884_, 2);
v___x_903_ = l_Lean_Syntax_node1(v___x_884_, v___x_902_, v___x_892_);
v___x_904_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7));
v___x_905_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8));
v___x_906_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_904_, v___x_905_);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 2);
lean_ctor_set(v___x_873_, 1, v___x_905_);
lean_ctor_set(v___x_873_, 0, v___x_884_);
v___x_908_ = v___x_873_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v___x_905_);
v___x_908_ = v_reuseFailAlloc_1138_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc_n(v___x_884_, 97);
v___x_909_ = l_Lean_Syntax_node2(v___x_884_, v___x_906_, v___x_908_, v___x_861_);
v___x_910_ = l_Lean_Syntax_node2(v___x_884_, v___x_900_, v___x_903_, v___x_909_);
v___x_911_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9));
v___x_913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_884_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
lean_inc_ref_n(v___x_913_, 2);
v___x_914_ = l_Lean_Syntax_node3(v___x_884_, v___x_895_, v___x_898_, v___x_911_, v___x_913_);
v___x_915_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v___x_914_);
v___x_916_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10));
lean_inc_ref_n(v___x_860_, 27);
lean_inc_ref_n(v___x_859_, 29);
v___x_917_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_916_);
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_884_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
v___x_919_ = l_Lean_Syntax_node1(v___x_884_, v___x_917_, v___x_918_);
v___x_920_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v___x_919_);
lean_inc_ref_n(v___x_892_, 32);
v___x_921_ = l_Lean_Syntax_node7(v___x_884_, v___x_890_, v___x_892_, v___x_915_, v___x_892_, v___x_892_, v___x_920_, v___x_892_, v___x_892_);
v___x_922_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11));
v___x_923_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12));
v___x_925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_884_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13));
v___x_927_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15);
v___x_929_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16));
lean_inc_n(v_currMacroScope_881_, 13);
lean_inc_n(v_quotContext_880_, 13);
v___x_930_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_929_, v_currMacroScope_881_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_932_, 0, v___x_884_);
lean_ctor_set(v___x_932_, 1, v___x_928_);
lean_ctor_set(v___x_932_, 2, v___x_930_);
lean_ctor_set(v___x_932_, 3, v___x_931_);
v___x_933_ = l_Lean_Syntax_node2(v___x_884_, v___x_927_, v___x_932_, v___x_892_);
v___x_934_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17));
v___x_935_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18));
v___x_937_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_936_);
v___x_938_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_884_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20));
v___x_941_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21);
v___x_942_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22));
v___x_943_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_942_, v_currMacroScope_881_);
v___x_944_ = l_Lean_Name_mkStr2(v___x_859_, v___x_940_);
lean_inc(v___x_944_);
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_931_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_931_);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_949_, 0, v___x_884_);
lean_ctor_set(v___x_949_, 1, v___x_941_);
lean_ctor_set(v___x_949_, 2, v___x_943_);
lean_ctor_set(v___x_949_, 3, v___x_948_);
v___x_950_ = l_Lean_Syntax_node2(v___x_884_, v___x_937_, v___x_939_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v___x_950_);
v___x_952_ = l_Lean_Syntax_node2(v___x_884_, v___x_935_, v___x_892_, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23));
v___x_954_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_886_, v___x_953_);
v___x_955_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_884_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24));
v___x_958_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_957_);
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_884_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
v___x_960_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25));
v___x_961_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_960_);
v___x_962_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27);
v___x_963_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28));
v___x_964_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_963_, v_currMacroScope_881_);
v___x_965_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_965_, 0, v___x_884_);
lean_ctor_set(v___x_965_, 1, v___x_962_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
lean_ctor_set(v___x_965_, 3, v___x_931_);
lean_inc_ref_n(v___x_965_, 3);
v___x_966_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v___x_965_);
v___x_967_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_884_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30));
v___x_970_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_969_);
v___x_971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_884_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
v___x_972_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31));
v___x_973_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32));
v___x_975_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33));
v___x_977_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34));
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_884_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35));
v___x_981_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___x_884_, v___x_981_, v___x_892_);
v___x_983_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36));
v___x_984_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38);
v___x_986_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39));
v___x_987_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_986_, v_currMacroScope_881_);
v___x_988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_988_, 0, v___x_884_);
lean_ctor_set(v___x_988_, 1, v___x_985_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
lean_ctor_set(v___x_988_, 3, v___x_931_);
v___x_989_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_884_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41));
v___x_992_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42));
v___x_994_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43));
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_884_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_inc_ref(v___x_862_);
v___x_997_ = l_String_toRawSubstring_x27(v___x_862_);
v___x_998_ = l_Lean_Name_mkStr1(v___x_862_);
v___x_999_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_998_, v_currMacroScope_881_);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_863_);
lean_ctor_set(v___x_1000_, 1, v___x_931_);
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_931_);
v___x_1002_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1002_, 0, v___x_884_);
lean_ctor_set(v___x_1002_, 1, v___x_997_);
lean_ctor_set(v___x_1002_, 2, v___x_999_);
lean_ctor_set(v___x_1002_, 3, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44));
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_884_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_884_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
lean_inc_ref_n(v___x_1006_, 3);
v___x_1007_ = l_Lean_Syntax_node5(v___x_884_, v___x_994_, v___x_996_, v___x_1002_, v___x_1004_, v___x_864_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node1(v___x_884_, v___x_992_, v___x_1007_);
lean_inc_ref(v___x_988_);
v___x_1009_ = l_Lean_Syntax_node4(v___x_884_, v___x_984_, v___x_988_, v___x_892_, v___x_990_, v___x_1008_);
lean_inc_n(v___x_982_, 4);
lean_inc_ref_n(v___x_979_, 4);
v___x_1010_ = l_Lean_Syntax_node4(v___x_884_, v___x_977_, v___x_979_, v___x_892_, v___x_982_, v___x_1009_);
lean_inc_n(v___x_975_, 5);
v___x_1011_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1010_, v___x_892_);
v___x_1012_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45));
v___x_1013_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46));
v___x_1015_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47));
v___x_1017_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48));
v___x_1019_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node1(v___x_884_, v___x_1019_, v___x_965_);
v___x_1021_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49));
v___x_1022_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51);
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53));
v___x_1025_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1024_, v_currMacroScope_881_);
v___x_1026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1026_, 0, v___x_884_);
lean_ctor_set(v___x_1026_, 1, v___x_1023_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
lean_ctor_set(v___x_1026_, 3, v___x_931_);
v___x_1027_ = l_Lean_Syntax_node1(v___x_884_, v___x_885_, v_fst_871_);
lean_inc_n(v___x_1022_, 4);
v___x_1028_ = l_Lean_Syntax_node2(v___x_884_, v___x_1022_, v___x_1026_, v___x_1027_);
lean_inc_ref_n(v___x_956_, 5);
lean_inc_n(v___x_1020_, 3);
lean_inc_n(v___x_1017_, 3);
v___x_1029_ = l_Lean_Syntax_node5(v___x_884_, v___x_1017_, v___x_1020_, v___x_892_, v___x_892_, v___x_956_, v___x_1028_);
lean_inc_n(v___x_1015_, 3);
v___x_1030_ = l_Lean_Syntax_node1(v___x_884_, v___x_1015_, v___x_1029_);
lean_inc_n(v___x_1013_, 3);
v___x_1031_ = l_Lean_Syntax_node4(v___x_884_, v___x_1013_, v___x_979_, v___x_892_, v___x_982_, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1031_, v___x_892_);
v___x_1033_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55);
v___x_1034_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57));
v___x_1035_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1034_, v_currMacroScope_881_);
v___x_1036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1036_, 0, v___x_884_);
lean_ctor_set(v___x_1036_, 1, v___x_1033_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
lean_ctor_set(v___x_1036_, 3, v___x_931_);
v___x_1037_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59));
v___x_1038_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60));
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_884_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_Syntax_node1(v___x_884_, v___x_1037_, v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61));
v___x_1042_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62));
v___x_1044_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_884_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64));
v___x_1048_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66);
v___x_1049_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_865_, v_currMacroScope_881_);
lean_inc_ref(v___x_866_);
v___x_1050_ = l_Lean_Name_mkStr3(v___x_859_, v___x_860_, v___x_866_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_931_);
v___x_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_884_);
lean_ctor_set(v___x_1053_, 1, v___x_1048_);
lean_ctor_set(v___x_1053_, 2, v___x_1049_);
lean_ctor_set(v___x_1053_, 3, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node1(v___x_884_, v___x_1047_, v___x_1053_);
lean_inc_ref(v___x_1046_);
v___x_1055_ = l_Lean_Syntax_node2(v___x_884_, v___x_1044_, v___x_1046_, v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67));
v___x_1057_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68);
v___x_1058_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69));
v___x_1059_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1058_, v_currMacroScope_881_);
v___x_1060_ = l_Lean_Name_mkStr2(v___x_859_, v___x_1056_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_931_);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_931_);
v___x_1063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1063_, 0, v___x_884_);
lean_ctor_set(v___x_1063_, 1, v___x_1057_);
lean_ctor_set(v___x_1063_, 2, v___x_1059_);
lean_ctor_set(v___x_1063_, 3, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71));
v___x_1065_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72));
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_884_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_inc(v___x_1040_);
lean_inc_ref(v___x_1066_);
v___x_1067_ = l_Lean_Syntax_node4(v___x_884_, v___x_1064_, v___x_965_, v___x_1066_, v___x_1040_, v___x_913_);
v___x_1068_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73));
v___x_1069_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75);
v___x_1071_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76));
v___x_1072_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1071_, v_currMacroScope_881_);
v___x_1073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1073_, 0, v___x_884_);
lean_ctor_set(v___x_1073_, 1, v___x_1070_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
lean_ctor_set(v___x_1073_, 3, v___x_931_);
v___x_1074_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
v___x_1075_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78));
v___x_1076_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1075_, v_currMacroScope_881_);
v___x_1077_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82));
v___x_1078_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1078_, 0, v___x_884_);
lean_ctor_set(v___x_1078_, 1, v___x_1074_);
lean_ctor_set(v___x_1078_, 2, v___x_1076_);
lean_ctor_set(v___x_1078_, 3, v___x_1077_);
v___x_1079_ = l_Lean_Syntax_node5(v___x_884_, v___x_1069_, v___x_1046_, v___x_1073_, v___x_956_, v___x_1078_, v___x_1006_);
v___x_1080_ = l_Lean_Syntax_node3(v___x_884_, v___x_885_, v___x_1067_, v_fst_875_, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_884_, v___x_1022_, v___x_1063_, v___x_1080_);
lean_inc(v___x_1055_);
lean_inc(v___x_1042_);
v___x_1082_ = l_Lean_Syntax_node3(v___x_884_, v___x_1042_, v___x_1055_, v___x_1081_, v___x_1006_);
v___x_1083_ = l_Lean_Syntax_node2(v___x_884_, v___x_885_, v___x_1040_, v___x_1082_);
lean_inc_ref(v___x_1036_);
v___x_1084_ = l_Lean_Syntax_node2(v___x_884_, v___x_1022_, v___x_1036_, v___x_1083_);
v___x_1085_ = l_Lean_Syntax_node5(v___x_884_, v___x_1017_, v___x_1020_, v___x_892_, v___x_892_, v___x_956_, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_node1(v___x_884_, v___x_1015_, v___x_1085_);
v___x_1087_ = l_Lean_Syntax_node4(v___x_884_, v___x_1013_, v___x_979_, v___x_892_, v___x_982_, v___x_1086_);
v___x_1088_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1087_, v___x_892_);
v___x_1089_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83));
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_884_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_884_, v___x_1037_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84));
v___x_1093_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85);
v___x_1094_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86));
v___x_1095_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1094_, v_currMacroScope_881_);
v___x_1096_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_866_, v___x_1092_);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_931_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_931_);
v___x_1099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1099_, 0, v___x_884_);
lean_ctor_set(v___x_1099_, 1, v___x_1093_);
lean_ctor_set(v___x_1099_, 2, v___x_1095_);
lean_ctor_set(v___x_1099_, 3, v___x_1098_);
lean_inc(v___x_1091_);
v___x_1100_ = l_Lean_Syntax_node4(v___x_884_, v___x_1064_, v___x_965_, v___x_1066_, v___x_1091_, v___x_913_);
v___x_1101_ = l_Lean_Syntax_node2(v___x_884_, v___x_885_, v___x_1100_, v___x_988_);
v___x_1102_ = l_Lean_Syntax_node2(v___x_884_, v___x_1022_, v___x_1099_, v___x_1101_);
v___x_1103_ = l_Lean_Syntax_node3(v___x_884_, v___x_1042_, v___x_1055_, v___x_1102_, v___x_1006_);
v___x_1104_ = l_Lean_Syntax_node2(v___x_884_, v___x_885_, v___x_1091_, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_node2(v___x_884_, v___x_1022_, v___x_1036_, v___x_1104_);
v___x_1106_ = l_Lean_Syntax_node5(v___x_884_, v___x_1017_, v___x_1020_, v___x_892_, v___x_892_, v___x_956_, v___x_1105_);
v___x_1107_ = l_Lean_Syntax_node1(v___x_884_, v___x_1015_, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node4(v___x_884_, v___x_1013_, v___x_979_, v___x_892_, v___x_982_, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1108_, v___x_892_);
v___x_1110_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88);
v___x_1111_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90));
v___x_1112_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_1111_, v_currMacroScope_881_);
v___x_1113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1113_, 0, v___x_884_);
lean_ctor_set(v___x_1113_, 1, v___x_1110_);
lean_ctor_set(v___x_1113_, 2, v___x_1112_);
lean_ctor_set(v___x_1113_, 3, v___x_931_);
v___x_1114_ = l_Lean_Syntax_node5(v___x_884_, v___x_1017_, v___x_1020_, v___x_892_, v___x_892_, v___x_956_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node1(v___x_884_, v___x_1015_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node4(v___x_884_, v___x_1013_, v___x_979_, v___x_892_, v___x_982_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1116_, v___x_892_);
v___x_1118_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91));
v___x_1119_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_893_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_884_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
lean_inc(v___x_966_);
v___x_1122_ = l_Lean_Syntax_node2(v___x_884_, v___x_1119_, v___x_1121_, v___x_966_);
v___x_1123_ = l_Lean_Syntax_node2(v___x_884_, v___x_975_, v___x_1122_, v___x_892_);
v___x_1124_ = l_Lean_Syntax_node6(v___x_884_, v___x_885_, v___x_1011_, v___x_1032_, v___x_1088_, v___x_1109_, v___x_1117_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node1(v___x_884_, v___x_973_, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node2(v___x_884_, v___x_970_, v___x_971_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node4(v___x_884_, v___x_961_, v___x_966_, v___x_892_, v___x_968_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node2(v___x_884_, v___x_958_, v___x_959_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93));
v___x_1130_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94));
v___x_1131_ = l_Lean_Name_mkStr4(v___x_859_, v___x_860_, v___x_1129_, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_node2(v___x_884_, v___x_1131_, v___x_892_, v___x_892_);
v___x_1133_ = l_Lean_Syntax_node4(v___x_884_, v___x_954_, v___x_956_, v___x_1128_, v___x_1132_, v___x_892_);
v___x_1134_ = l_Lean_Syntax_node5(v___x_884_, v___x_923_, v___x_925_, v___x_933_, v___x_952_, v___x_1133_, v___x_892_);
v___x_1135_ = l_Lean_Syntax_node2(v___x_884_, v___x_888_, v___x_921_, v___x_1134_);
v___x_1136_ = l_Lean_Syntax_node2(v___x_884_, v___x_885_, v_snd_876_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_869_);
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___boxed(lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v___x_1149_, lean_object* v_____x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1142_, v___x_1143_, v___x_1144_, v___x_1145_, v___x_1146_, v___x_1147_, v___x_1148_, v___x_1149_, v_____x_1150_, v___y_1151_, v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(uint8_t v___x_1154_, lean_object* v_____do__lift_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1155_, v___x_1154_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(lean_object* v___x_1160_, lean_object* v_____do__lift_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_39997__boxed_1164_; lean_object* v_res_1165_; 
v___x_39997__boxed_1164_ = lean_unbox(v___x_1160_);
v_res_1165_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_39997__boxed_1164_, v_____do__lift_1161_, v___y_1162_, v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_____do__lift_1161_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1181_ = l_String_toRawSubstring_x27(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11));
v___x_1194_ = l_String_toRawSubstring_x27(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25));
v___x_1220_ = l_String_toRawSubstring_x27(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30));
v___x_1231_ = l_String_toRawSubstring_x27(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34));
v___x_1241_ = l_String_toRawSubstring_x27(v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40));
v___x_1253_ = l_String_toRawSubstring_x27(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44));
v___x_1263_ = l_String_toRawSubstring_x27(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_1274_ = l_String_toRawSubstring_x27(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58));
v___x_1297_ = l_String_toRawSubstring_x27(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_1314_ = l_String_toRawSubstring_x27(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(lean_object* v_x_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___y_1333_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1343_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0));
v___x_1344_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1));
v___x_1345_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__0));
v___x_1346_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
lean_inc(v_x_1329_);
v___x_1347_ = l_Lean_Syntax_isOfKind(v_x_1329_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_x_1329_);
v___x_1348_ = lean_box(1);
v___x_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_a_1331_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1786_; lean_object* v___x_1925_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = l_Lean_Syntax_getArg(v_x_1329_, v___x_1350_);
v___x_1352_ = lean_unsigned_to_nat(2u);
v___x_1353_ = l_Lean_Syntax_getArg(v_x_1329_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(4u);
v___x_1355_ = l_Lean_Syntax_getArg(v_x_1329_, v___x_1354_);
v___x_1356_ = lean_unsigned_to_nat(6u);
v___x_1357_ = l_Lean_Syntax_getArg(v_x_1329_, v___x_1356_);
v___x_1358_ = lean_unsigned_to_nat(8u);
v___x_1359_ = l_Lean_Syntax_getArg(v_x_1329_, v___x_1358_);
lean_dec(v_x_1329_);
v___x_1360_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1361_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_1362_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27));
v___x_1363_ = lean_box(0);
v___x_1925_ = l_Lean_Syntax_getOptional_x3f(v___x_1351_);
lean_dec(v___x_1351_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_box(0);
v___y_1786_ = v___x_1926_;
goto v___jp_1785_;
}
else
{
lean_object* v_val_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_val_1927_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1925_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_val_1927_);
lean_dec(v___x_1925_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_val_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
v___y_1786_ = v___x_1932_;
goto v___jp_1785_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc_ref_n(v___y_1378_, 2);
v___x_1380_ = l_Array_append___redArg(v___y_1378_, v___y_1379_);
lean_dec_ref(v___y_1379_);
lean_inc_n(v___y_1370_, 9);
lean_inc_n(v___y_1372_, 56);
v___x_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1372_);
lean_ctor_set(v___x_1381_, 1, v___y_1370_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1382_, 0, v___y_1372_);
lean_ctor_set(v___x_1382_, 1, v___y_1370_);
lean_ctor_set(v___x_1382_, 2, v___y_1378_);
v___x_1383_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
lean_inc_ref(v___y_1375_);
v___x_1384_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1375_, v___x_1383_);
lean_inc_ref_n(v___x_1382_, 9);
v___x_1385_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1384_, v___x_1382_);
lean_inc_ref(v___y_1365_);
v___x_1386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1372_);
lean_ctor_set(v___x_1386_, 1, v___y_1365_);
v___x_1387_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1368_);
v___x_1388_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1368_, v___x_1387_);
v___x_1389_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___y_1372_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1372_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1372_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1372_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
lean_inc_ref_n(v___x_1396_, 5);
lean_inc(v___x_1355_);
lean_inc_ref_n(v___x_1390_, 5);
v___x_1397_ = l_Lean_Syntax_node5(v___y_1372_, v___x_1388_, v___x_1390_, v___x_1392_, v___x_1394_, v___x_1355_, v___x_1396_);
v___x_1398_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1370_, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1400_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1399_, v___x_1357_);
v___x_1401_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1402_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1403_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1371_, 6);
lean_inc_n(v___y_1369_, 6);
v___x_1404_ = l_Lean_addMacroScope(v___y_1369_, v___x_1403_, v___y_1371_);
lean_inc_n(v___y_1377_, 6);
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1361_);
lean_ctor_set(v___x_1405_, 1, v___y_1377_);
lean_inc_n(v___y_1373_, 7);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___y_1373_);
v___x_1407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1372_);
lean_ctor_set(v___x_1407_, 1, v___x_1402_);
lean_ctor_set(v___x_1407_, 2, v___x_1404_);
lean_ctor_set(v___x_1407_, 3, v___x_1406_);
v___x_1408_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1407_, v___x_1382_);
v___x_1409_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1410_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1411_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1412_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1413_ = l_Lean_addMacroScope(v___y_1369_, v___x_1412_, v___y_1371_);
v___x_1414_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___y_1377_);
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v___y_1373_);
v___x_1417_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1417_, 0, v___y_1372_);
lean_ctor_set(v___x_1417_, 1, v___x_1411_);
lean_ctor_set(v___x_1417_, 2, v___x_1413_);
lean_ctor_set(v___x_1417_, 3, v___x_1416_);
v___x_1418_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1417_, v___x_1382_);
v___x_1419_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1370_, v___x_1418_);
v___x_1420_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1410_, v___x_1390_, v___x_1419_, v___x_1396_);
v___x_1421_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1372_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
lean_inc_ref_n(v___x_1422_, 3);
v___x_1423_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1409_, v___x_1420_, v___x_1422_);
v___x_1424_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1425_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1372_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1372_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1362_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1424_, v___x_1426_, v___x_1429_);
v___x_1431_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1370_, v___x_1430_);
v___x_1432_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1410_, v___x_1390_, v___x_1431_, v___x_1396_);
v___x_1433_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1409_, v___x_1432_, v___x_1422_);
v___x_1434_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1372_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1362_, v___x_1435_);
v___x_1437_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1399_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1439_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1440_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
v___x_1441_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27));
v___x_1442_ = l_Lean_addMacroScope(v___y_1369_, v___x_1441_, v___y_1371_);
v___x_1443_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28));
v___x_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___y_1377_);
v___x_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___y_1373_);
v___x_1446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1372_);
lean_ctor_set(v___x_1446_, 1, v___x_1440_);
lean_ctor_set(v___x_1446_, 2, v___x_1442_);
lean_ctor_set(v___x_1446_, 3, v___x_1445_);
v___x_1447_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1446_, v___x_1382_);
v___x_1448_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1372_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1451_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1452_ = l_Lean_addMacroScope(v___y_1369_, v___x_1451_, v___y_1371_);
v___x_1453_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___y_1377_);
v___x_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___y_1373_);
v___x_1456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1372_);
lean_ctor_set(v___x_1456_, 1, v___x_1450_);
lean_ctor_set(v___x_1456_, 2, v___x_1452_);
lean_ctor_set(v___x_1456_, 3, v___x_1455_);
v___x_1457_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1456_, v___x_1382_);
v___x_1458_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1459_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
v___x_1460_ = l_Lean_addMacroScope(v___y_1369_, v___x_1459_, v___y_1371_);
v___x_1461_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___y_1377_);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___y_1373_);
v___x_1464_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1372_);
lean_ctor_set(v___x_1464_, 1, v___x_1458_);
lean_ctor_set(v___x_1464_, 2, v___x_1460_);
lean_ctor_set(v___x_1464_, 3, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1464_, v___x_1382_);
lean_inc_ref(v___x_1449_);
v___x_1466_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1439_, v___x_1457_, v___x_1449_, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1439_, v___x_1447_, v___x_1449_, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1370_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1410_, v___x_1390_, v___x_1468_, v___x_1396_);
v___x_1470_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1372_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1438_, v___x_1469_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
v___x_1474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1372_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1362_, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1399_, v___x_1475_);
v___x_1477_ = l_Lean_Syntax_node3(v___y_1372_, v___y_1370_, v___x_1437_, v___x_1472_, v___x_1476_);
v___x_1478_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1410_, v___x_1390_, v___x_1477_, v___x_1396_);
v___x_1479_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1409_, v___x_1478_, v___x_1422_);
v___x_1480_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
v___x_1481_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
v___x_1482_ = l_Lean_addMacroScope(v___y_1369_, v___x_1481_, v___y_1371_);
v___x_1483_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43));
v___x_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___y_1377_);
v___x_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___y_1373_);
v___x_1486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1372_);
lean_ctor_set(v___x_1486_, 1, v___x_1480_);
lean_ctor_set(v___x_1486_, 2, v___x_1482_);
lean_ctor_set(v___x_1486_, 3, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1401_, v___x_1486_, v___x_1382_);
v___x_1488_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1370_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node3(v___y_1372_, v___x_1410_, v___x_1390_, v___x_1488_, v___x_1396_);
v___x_1490_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1409_, v___x_1489_, v___x_1422_);
v___x_1491_ = l_Lean_Syntax_node6(v___y_1372_, v___y_1370_, v___x_1400_, v___x_1408_, v___x_1423_, v___x_1433_, v___x_1479_, v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
v___x_1493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___y_1372_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1496_ = l_Lean_addMacroScope(v___y_1369_, v___x_1495_, v___y_1371_);
v___x_1497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1497_, 0, v___y_1372_);
lean_ctor_set(v___x_1497_, 1, v___x_1494_);
lean_ctor_set(v___x_1497_, 2, v___x_1496_);
lean_ctor_set(v___x_1497_, 3, v___y_1373_);
v___x_1498_ = lean_unsigned_to_nat(10u);
v___x_1499_ = lean_mk_empty_array_with_capacity(v___x_1498_);
v___x_1500_ = lean_array_push(v___x_1499_, v___x_1381_);
v___x_1501_ = lean_array_push(v___x_1500_, v___x_1382_);
v___x_1502_ = lean_array_push(v___x_1501_, v___x_1385_);
v___x_1503_ = lean_array_push(v___x_1502_, v___x_1386_);
v___x_1504_ = lean_array_push(v___x_1503_, v___x_1382_);
v___x_1505_ = lean_array_push(v___x_1504_, v___x_1398_);
v___x_1506_ = lean_array_push(v___x_1505_, v___x_1382_);
v___x_1507_ = lean_array_push(v___x_1506_, v___x_1491_);
v___x_1508_ = lean_array_push(v___x_1507_, v___x_1493_);
v___x_1509_ = lean_array_push(v___x_1508_, v___x_1497_);
lean_inc(v___y_1374_);
v___x_1510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1372_);
lean_ctor_set(v___x_1510_, 1, v___y_1374_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___y_1376_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___y_1366_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1343_, v___x_1344_, v___x_1355_, v___x_1360_, v___x_1361_, v___x_1359_, v___x_1363_, v___x_1345_, v___x_1512_, v_a_1330_, v___y_1367_);
v___y_1333_ = v___x_1513_;
goto v___jp_1332_;
}
v___jp_1514_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_inc_ref_n(v___y_1522_, 2);
v___x_1530_ = l_Array_append___redArg(v___y_1522_, v___y_1529_);
lean_dec_ref(v___y_1529_);
lean_inc_n(v___y_1519_, 9);
lean_inc_n(v___y_1516_, 53);
v___x_1531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___y_1516_);
lean_ctor_set(v___x_1531_, 1, v___y_1519_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1516_);
lean_ctor_set(v___x_1532_, 1, v___y_1519_);
lean_ctor_set(v___x_1532_, 2, v___y_1522_);
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
lean_inc_ref(v___y_1521_);
v___x_1534_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1521_, v___x_1533_);
lean_inc_ref_n(v___x_1532_, 8);
v___x_1535_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1534_, v___x_1532_);
lean_inc_ref(v___y_1523_);
v___x_1536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___y_1516_);
lean_ctor_set(v___x_1536_, 1, v___y_1523_);
v___x_1537_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1528_);
v___x_1538_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1528_, v___x_1537_);
v___x_1539_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___y_1516_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___y_1516_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___y_1516_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___y_1516_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
lean_inc_ref_n(v___x_1546_, 5);
lean_inc(v___x_1355_);
lean_inc_ref_n(v___x_1540_, 5);
v___x_1547_ = l_Lean_Syntax_node5(v___y_1516_, v___x_1538_, v___x_1540_, v___x_1542_, v___x_1544_, v___x_1355_, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node1(v___y_1516_, v___y_1519_, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1550_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1549_, v___x_1357_);
v___x_1551_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1552_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1553_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1517_, 5);
lean_inc_n(v___y_1525_, 5);
v___x_1554_ = l_Lean_addMacroScope(v___y_1525_, v___x_1553_, v___y_1517_);
lean_inc_n(v___y_1520_, 5);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1361_);
lean_ctor_set(v___x_1555_, 1, v___y_1520_);
lean_inc_n(v___y_1526_, 6);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___y_1526_);
v___x_1557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1516_);
lean_ctor_set(v___x_1557_, 1, v___x_1552_);
lean_ctor_set(v___x_1557_, 2, v___x_1554_);
lean_ctor_set(v___x_1557_, 3, v___x_1556_);
v___x_1558_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1551_, v___x_1557_, v___x_1532_);
v___x_1559_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1560_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1561_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1562_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1563_ = l_Lean_addMacroScope(v___y_1525_, v___x_1562_, v___y_1517_);
v___x_1564_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___y_1520_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___y_1526_);
v___x_1567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1567_, 0, v___y_1516_);
lean_ctor_set(v___x_1567_, 1, v___x_1561_);
lean_ctor_set(v___x_1567_, 2, v___x_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1551_, v___x_1567_, v___x_1532_);
v___x_1569_ = l_Lean_Syntax_node1(v___y_1516_, v___y_1519_, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1560_, v___x_1540_, v___x_1569_, v___x_1546_);
v___x_1571_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___y_1516_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_inc_ref_n(v___x_1572_, 3);
v___x_1573_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1559_, v___x_1570_, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1575_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___y_1516_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1516_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1362_, v___x_1578_);
v___x_1580_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1574_, v___x_1576_, v___x_1579_);
v___x_1581_ = l_Lean_Syntax_node1(v___y_1516_, v___y_1519_, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1560_, v___x_1540_, v___x_1581_, v___x_1546_);
v___x_1583_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1559_, v___x_1582_, v___x_1572_);
v___x_1584_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1516_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1362_, v___x_1585_);
v___x_1587_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1549_, v___x_1586_);
v___x_1588_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1589_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1590_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1591_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1592_ = l_Lean_addMacroScope(v___y_1525_, v___x_1591_, v___y_1517_);
v___x_1593_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___y_1520_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___y_1526_);
v___x_1596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1516_);
lean_ctor_set(v___x_1596_, 1, v___x_1590_);
lean_ctor_set(v___x_1596_, 2, v___x_1592_);
lean_ctor_set(v___x_1596_, 3, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1551_, v___x_1596_, v___x_1532_);
v___x_1598_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1516_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1601_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
v___x_1602_ = l_Lean_addMacroScope(v___y_1525_, v___x_1601_, v___y_1517_);
v___x_1603_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___y_1520_);
v___x_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v___y_1526_);
v___x_1606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1516_);
lean_ctor_set(v___x_1606_, 1, v___x_1600_);
lean_ctor_set(v___x_1606_, 2, v___x_1602_);
lean_ctor_set(v___x_1606_, 3, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1551_, v___x_1606_, v___x_1532_);
v___x_1608_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1589_, v___x_1597_, v___x_1599_, v___x_1607_);
v___x_1609_ = l_Lean_Syntax_node1(v___y_1516_, v___y_1519_, v___x_1608_);
v___x_1610_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1560_, v___x_1540_, v___x_1609_, v___x_1546_);
v___x_1611_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1516_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1588_, v___x_1610_, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
v___x_1615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1516_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1362_, v___x_1615_);
v___x_1617_ = l_Lean_Syntax_node1(v___y_1516_, v___x_1549_, v___x_1616_);
v___x_1618_ = l_Lean_Syntax_node3(v___y_1516_, v___y_1519_, v___x_1587_, v___x_1613_, v___x_1617_);
v___x_1619_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1560_, v___x_1540_, v___x_1618_, v___x_1546_);
v___x_1620_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1559_, v___x_1619_, v___x_1572_);
v___x_1621_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
v___x_1622_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
v___x_1623_ = l_Lean_addMacroScope(v___y_1525_, v___x_1622_, v___y_1517_);
v___x_1624_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43));
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___y_1520_);
v___x_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v___y_1526_);
v___x_1627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1516_);
lean_ctor_set(v___x_1627_, 1, v___x_1621_);
lean_ctor_set(v___x_1627_, 2, v___x_1623_);
lean_ctor_set(v___x_1627_, 3, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1551_, v___x_1627_, v___x_1532_);
v___x_1629_ = l_Lean_Syntax_node1(v___y_1516_, v___y_1519_, v___x_1628_);
v___x_1630_ = l_Lean_Syntax_node3(v___y_1516_, v___x_1560_, v___x_1540_, v___x_1629_, v___x_1546_);
v___x_1631_ = l_Lean_Syntax_node2(v___y_1516_, v___x_1559_, v___x_1630_, v___x_1572_);
v___x_1632_ = l_Lean_Syntax_node6(v___y_1516_, v___y_1519_, v___x_1550_, v___x_1558_, v___x_1573_, v___x_1583_, v___x_1620_, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
v___x_1634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1516_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1637_ = l_Lean_addMacroScope(v___y_1525_, v___x_1636_, v___y_1517_);
v___x_1638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1516_);
lean_ctor_set(v___x_1638_, 1, v___x_1635_);
lean_ctor_set(v___x_1638_, 2, v___x_1637_);
lean_ctor_set(v___x_1638_, 3, v___y_1526_);
v___x_1639_ = lean_unsigned_to_nat(10u);
v___x_1640_ = lean_mk_empty_array_with_capacity(v___x_1639_);
v___x_1641_ = lean_array_push(v___x_1640_, v___x_1531_);
v___x_1642_ = lean_array_push(v___x_1641_, v___x_1532_);
v___x_1643_ = lean_array_push(v___x_1642_, v___x_1535_);
v___x_1644_ = lean_array_push(v___x_1643_, v___x_1536_);
v___x_1645_ = lean_array_push(v___x_1644_, v___x_1532_);
v___x_1646_ = lean_array_push(v___x_1645_, v___x_1548_);
v___x_1647_ = lean_array_push(v___x_1646_, v___x_1532_);
v___x_1648_ = lean_array_push(v___x_1647_, v___x_1632_);
v___x_1649_ = lean_array_push(v___x_1648_, v___x_1634_);
v___x_1650_ = lean_array_push(v___x_1649_, v___x_1638_);
lean_inc(v___y_1515_);
v___x_1651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1516_);
lean_ctor_set(v___x_1651_, 1, v___y_1515_);
lean_ctor_set(v___x_1651_, 2, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___y_1518_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1527_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1343_, v___x_1344_, v___x_1355_, v___x_1360_, v___x_1361_, v___x_1359_, v___x_1363_, v___x_1345_, v___x_1653_, v_a_1330_, v___y_1524_);
v___y_1333_ = v___x_1654_;
goto v___jp_1332_;
}
v___jp_1655_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_inc_ref_n(v___y_1656_, 2);
v___x_1671_ = l_Array_append___redArg(v___y_1656_, v___y_1670_);
lean_dec_ref(v___y_1670_);
lean_inc_n(v___y_1660_, 8);
lean_inc_n(v___y_1659_, 48);
v___x_1672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1659_);
lean_ctor_set(v___x_1672_, 1, v___y_1660_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1659_);
lean_ctor_set(v___x_1673_, 1, v___y_1660_);
lean_ctor_set(v___x_1673_, 2, v___y_1656_);
v___x_1674_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6));
lean_inc_ref(v___y_1662_);
v___x_1675_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1662_, v___x_1674_);
lean_inc_ref_n(v___x_1673_, 7);
v___x_1676_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1675_, v___x_1673_);
lean_inc_ref(v___y_1666_);
v___x_1677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1659_);
lean_ctor_set(v___x_1677_, 1, v___y_1666_);
v___x_1678_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1663_);
v___x_1679_ = l_Lean_Name_mkStr4(v___x_1343_, v___x_1344_, v___y_1663_, v___x_1678_);
v___x_1680_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___y_1659_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1659_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___y_1659_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___y_1659_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
lean_inc_ref_n(v___x_1687_, 4);
lean_inc(v___x_1355_);
lean_inc_ref_n(v___x_1681_, 4);
v___x_1688_ = l_Lean_Syntax_node5(v___y_1659_, v___x_1679_, v___x_1681_, v___x_1683_, v___x_1685_, v___x_1355_, v___x_1687_);
v___x_1689_ = l_Lean_Syntax_node1(v___y_1659_, v___y_1660_, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1691_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1690_, v___x_1357_);
v___x_1692_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1693_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1694_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1661_, 4);
lean_inc_n(v___y_1668_, 4);
v___x_1695_ = l_Lean_addMacroScope(v___y_1668_, v___x_1694_, v___y_1661_);
lean_inc_n(v___y_1664_, 4);
v___x_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1361_);
lean_ctor_set(v___x_1696_, 1, v___y_1664_);
lean_inc_n(v___y_1658_, 5);
v___x_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___y_1658_);
v___x_1698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1698_, 0, v___y_1659_);
lean_ctor_set(v___x_1698_, 1, v___x_1693_);
lean_ctor_set(v___x_1698_, 2, v___x_1695_);
lean_ctor_set(v___x_1698_, 3, v___x_1697_);
v___x_1699_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1692_, v___x_1698_, v___x_1673_);
v___x_1700_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1701_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1702_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1703_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1704_ = l_Lean_addMacroScope(v___y_1668_, v___x_1703_, v___y_1661_);
v___x_1705_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___y_1664_);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v___y_1658_);
v___x_1708_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1708_, 0, v___y_1659_);
lean_ctor_set(v___x_1708_, 1, v___x_1702_);
lean_ctor_set(v___x_1708_, 2, v___x_1704_);
lean_ctor_set(v___x_1708_, 3, v___x_1707_);
v___x_1709_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1692_, v___x_1708_, v___x_1673_);
v___x_1710_ = l_Lean_Syntax_node1(v___y_1659_, v___y_1660_, v___x_1709_);
v___x_1711_ = l_Lean_Syntax_node3(v___y_1659_, v___x_1701_, v___x_1681_, v___x_1710_, v___x_1687_);
v___x_1712_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___y_1659_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
lean_inc_ref_n(v___x_1713_, 2);
v___x_1714_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1700_, v___x_1711_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1716_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1659_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___y_1659_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1362_, v___x_1719_);
v___x_1721_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1715_, v___x_1717_, v___x_1720_);
v___x_1722_ = l_Lean_Syntax_node1(v___y_1659_, v___y_1660_, v___x_1721_);
v___x_1723_ = l_Lean_Syntax_node3(v___y_1659_, v___x_1701_, v___x_1681_, v___x_1722_, v___x_1687_);
v___x_1724_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1700_, v___x_1723_, v___x_1713_);
v___x_1725_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1659_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1362_, v___x_1726_);
v___x_1728_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1690_, v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1730_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1731_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1732_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1733_ = l_Lean_addMacroScope(v___y_1668_, v___x_1732_, v___y_1661_);
v___x_1734_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___y_1664_);
v___x_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___y_1658_);
v___x_1737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1659_);
lean_ctor_set(v___x_1737_, 1, v___x_1731_);
lean_ctor_set(v___x_1737_, 2, v___x_1733_);
lean_ctor_set(v___x_1737_, 3, v___x_1736_);
v___x_1738_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1692_, v___x_1737_, v___x_1673_);
v___x_1739_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1659_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
v___x_1742_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
v___x_1743_ = l_Lean_addMacroScope(v___y_1668_, v___x_1742_, v___y_1661_);
v___x_1744_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37));
v___x_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___y_1664_);
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___y_1658_);
v___x_1747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1747_, 0, v___y_1659_);
lean_ctor_set(v___x_1747_, 1, v___x_1741_);
lean_ctor_set(v___x_1747_, 2, v___x_1743_);
lean_ctor_set(v___x_1747_, 3, v___x_1746_);
v___x_1748_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1692_, v___x_1747_, v___x_1673_);
v___x_1749_ = l_Lean_Syntax_node3(v___y_1659_, v___x_1730_, v___x_1738_, v___x_1740_, v___x_1748_);
v___x_1750_ = l_Lean_Syntax_node1(v___y_1659_, v___y_1660_, v___x_1749_);
v___x_1751_ = l_Lean_Syntax_node3(v___y_1659_, v___x_1701_, v___x_1681_, v___x_1750_, v___x_1687_);
v___x_1752_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___y_1659_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1729_, v___x_1751_, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1659_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1362_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_node1(v___y_1659_, v___x_1690_, v___x_1757_);
v___x_1759_ = l_Lean_Syntax_node3(v___y_1659_, v___y_1660_, v___x_1728_, v___x_1754_, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node3(v___y_1659_, v___x_1701_, v___x_1681_, v___x_1759_, v___x_1687_);
v___x_1761_ = l_Lean_Syntax_node2(v___y_1659_, v___x_1700_, v___x_1760_, v___x_1713_);
v___x_1762_ = l_Lean_Syntax_node5(v___y_1659_, v___y_1660_, v___x_1691_, v___x_1699_, v___x_1714_, v___x_1724_, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19));
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___y_1659_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1767_ = l_Lean_addMacroScope(v___y_1668_, v___x_1766_, v___y_1661_);
v___x_1768_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1768_, 0, v___y_1659_);
lean_ctor_set(v___x_1768_, 1, v___x_1765_);
lean_ctor_set(v___x_1768_, 2, v___x_1767_);
lean_ctor_set(v___x_1768_, 3, v___y_1658_);
v___x_1769_ = lean_unsigned_to_nat(10u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_array_push(v___x_1770_, v___x_1672_);
v___x_1772_ = lean_array_push(v___x_1771_, v___x_1673_);
v___x_1773_ = lean_array_push(v___x_1772_, v___x_1676_);
v___x_1774_ = lean_array_push(v___x_1773_, v___x_1677_);
v___x_1775_ = lean_array_push(v___x_1774_, v___x_1673_);
v___x_1776_ = lean_array_push(v___x_1775_, v___x_1689_);
v___x_1777_ = lean_array_push(v___x_1776_, v___x_1673_);
v___x_1778_ = lean_array_push(v___x_1777_, v___x_1762_);
v___x_1779_ = lean_array_push(v___x_1778_, v___x_1764_);
v___x_1780_ = lean_array_push(v___x_1779_, v___x_1768_);
lean_inc(v___y_1657_);
v___x_1781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1659_);
lean_ctor_set(v___x_1781_, 1, v___y_1657_);
lean_ctor_set(v___x_1781_, 2, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1669_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___y_1667_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1343_, v___x_1344_, v___x_1355_, v___x_1360_, v___x_1361_, v___x_1359_, v___x_1363_, v___x_1345_, v___x_1783_, v_a_1330_, v___y_1665_);
v___y_1333_ = v___x_1784_;
goto v___jp_1332_;
}
v___jp_1785_:
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Syntax_isNone(v___x_1353_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1788_ = l_Lean_Syntax_getArg(v___x_1353_, v___x_1350_);
lean_dec(v___x_1353_);
v___x_1789_ = l_Lean_Syntax_getKind(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__1));
v___x_1791_ = lean_name_eq(v___x_1789_, v___x_1790_);
lean_dec(v___x_1789_);
if (v___x_1791_ == 0)
{
lean_object* v_quotContext_1792_; lean_object* v_currMacroScope_1793_; lean_object* v_ref_1794_; lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1835_; 
v_quotContext_1792_ = lean_ctor_get(v_a_1330_, 1);
v_currMacroScope_1793_ = lean_ctor_get(v_a_1330_, 2);
v_ref_1794_ = lean_ctor_get(v_a_1330_, 5);
v___x_1795_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1791_, v_ref_1794_, v_a_1330_, v_a_1331_);
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
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50);
v___x_1807_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51));
lean_inc(v_currMacroScope_1793_);
lean_inc(v_quotContext_1792_);
v___x_1808_ = l_Lean_addMacroScope(v_quotContext_1792_, v___x_1807_, v_currMacroScope_1793_);
v___x_1809_ = lean_box(0);
v___x_1810_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54));
lean_inc(v_a_1796_);
v___x_1811_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1796_);
lean_ctor_set(v___x_1811_, 1, v___x_1806_);
lean_ctor_set(v___x_1811_, 2, v___x_1808_);
lean_ctor_set(v___x_1811_, 3, v___x_1810_);
lean_inc_ref(v___x_1805_);
v___x_1812_ = l_Lean_Syntax_node3(v_a_1796_, v___x_1802_, v___x_1805_, v___x_1805_, v___x_1811_);
v___x_1813_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1791_, v_ref_1794_, v_a_1330_, v_a_1797_);
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
v___x_1819_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55));
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
v___x_1822_ = l_Lean_Syntax_node1(v_a_1814_, v___x_1362_, v___x_1821_);
v___x_1823_ = l_Lean_SourceInfo_fromRef(v_ref_1794_, v___x_1791_);
v___x_1824_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1825_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1826_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1827_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1828_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1786_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; 
v_val_1829_ = lean_ctor_get(v___y_1786_, 0);
lean_inc(v_val_1829_);
lean_dec_ref(v___y_1786_);
v___x_1830_ = l_Array_mkArray1___redArg(v_val_1829_);
lean_inc(v_quotContext_1792_);
lean_inc(v_currMacroScope_1793_);
v___y_1515_ = v___x_1826_;
v___y_1516_ = v___x_1823_;
v___y_1517_ = v_currMacroScope_1793_;
v___y_1518_ = v___x_1822_;
v___y_1519_ = v___x_1827_;
v___y_1520_ = v___x_1809_;
v___y_1521_ = v___x_1801_;
v___y_1522_ = v___x_1828_;
v___y_1523_ = v___x_1825_;
v___y_1524_ = v_a_1815_;
v___y_1525_ = v_quotContext_1792_;
v___y_1526_ = v___x_1809_;
v___y_1527_ = v___x_1812_;
v___y_1528_ = v___x_1824_;
v___y_1529_ = v___x_1830_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1831_; 
lean_dec(v___y_1786_);
v___x_1831_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1792_);
lean_inc(v_currMacroScope_1793_);
v___y_1515_ = v___x_1826_;
v___y_1516_ = v___x_1823_;
v___y_1517_ = v_currMacroScope_1793_;
v___y_1518_ = v___x_1822_;
v___y_1519_ = v___x_1827_;
v___y_1520_ = v___x_1809_;
v___y_1521_ = v___x_1801_;
v___y_1522_ = v___x_1828_;
v___y_1523_ = v___x_1825_;
v___y_1524_ = v_a_1815_;
v___y_1525_ = v_quotContext_1792_;
v___y_1526_ = v___x_1809_;
v___y_1527_ = v___x_1812_;
v___y_1528_ = v___x_1824_;
v___y_1529_ = v___x_1831_;
goto v___jp_1514_;
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1836_; lean_object* v_currMacroScope_1837_; lean_object* v_ref_1838_; lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1879_; 
v_quotContext_1836_ = lean_ctor_get(v_a_1330_, 1);
v_currMacroScope_1837_ = lean_ctor_get(v_a_1330_, 2);
v_ref_1838_ = lean_ctor_get(v_a_1330_, 5);
v___x_1839_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1838_, v_a_1330_, v_a_1331_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_a_1841_ = lean_ctor_get(v___x_1839_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1843_ = v___x_1839_;
v_isShared_1844_ = v_isSharedCheck_1879_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1879_;
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
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1840_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1877_; 
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59);
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60));
lean_inc(v_currMacroScope_1837_);
lean_inc(v_quotContext_1836_);
v___x_1852_ = l_Lean_addMacroScope(v_quotContext_1836_, v___x_1851_, v_currMacroScope_1837_);
v___x_1853_ = lean_box(0);
v___x_1854_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63));
lean_inc(v_a_1840_);
v___x_1855_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1855_, 0, v_a_1840_);
lean_ctor_set(v___x_1855_, 1, v___x_1850_);
lean_ctor_set(v___x_1855_, 2, v___x_1852_);
lean_ctor_set(v___x_1855_, 3, v___x_1854_);
lean_inc_ref(v___x_1849_);
v___x_1856_ = l_Lean_Syntax_node3(v_a_1840_, v___x_1846_, v___x_1849_, v___x_1849_, v___x_1855_);
v___x_1857_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1838_, v_a_1330_, v_a_1841_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_a_1859_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1877_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1877_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64));
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
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1858_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1866_ = l_Lean_Syntax_node1(v_a_1858_, v___x_1362_, v___x_1865_);
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_ref_1838_, v___x_1787_);
v___x_1868_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1869_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1870_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1871_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1872_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1786_) == 1)
{
lean_object* v_val_1873_; lean_object* v___x_1874_; 
v_val_1873_ = lean_ctor_get(v___y_1786_, 0);
lean_inc(v_val_1873_);
lean_dec_ref(v___y_1786_);
v___x_1874_ = l_Array_mkArray1___redArg(v_val_1873_);
lean_inc(v_quotContext_1836_);
lean_inc(v_currMacroScope_1837_);
v___y_1656_ = v___x_1872_;
v___y_1657_ = v___x_1870_;
v___y_1658_ = v___x_1853_;
v___y_1659_ = v___x_1867_;
v___y_1660_ = v___x_1871_;
v___y_1661_ = v_currMacroScope_1837_;
v___y_1662_ = v___x_1845_;
v___y_1663_ = v___x_1868_;
v___y_1664_ = v___x_1853_;
v___y_1665_ = v_a_1859_;
v___y_1666_ = v___x_1869_;
v___y_1667_ = v___x_1856_;
v___y_1668_ = v_quotContext_1836_;
v___y_1669_ = v___x_1866_;
v___y_1670_ = v___x_1874_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1875_; 
lean_dec(v___y_1786_);
v___x_1875_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1836_);
lean_inc(v_currMacroScope_1837_);
v___y_1656_ = v___x_1872_;
v___y_1657_ = v___x_1870_;
v___y_1658_ = v___x_1853_;
v___y_1659_ = v___x_1867_;
v___y_1660_ = v___x_1871_;
v___y_1661_ = v_currMacroScope_1837_;
v___y_1662_ = v___x_1845_;
v___y_1663_ = v___x_1868_;
v___y_1664_ = v___x_1853_;
v___y_1665_ = v_a_1859_;
v___y_1666_ = v___x_1869_;
v___y_1667_ = v___x_1856_;
v___y_1668_ = v_quotContext_1836_;
v___y_1669_ = v___x_1866_;
v___y_1670_ = v___x_1875_;
goto v___jp_1655_;
}
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1880_; lean_object* v_currMacroScope_1881_; lean_object* v_ref_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v___x_1353_);
v_quotContext_1880_ = lean_ctor_get(v_a_1330_, 1);
v_currMacroScope_1881_ = lean_ctor_get(v_a_1330_, 2);
v_ref_1882_ = lean_ctor_get(v_a_1330_, 5);
v___x_1883_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1882_, v_a_1330_, v_a_1331_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1924_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1924_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1889_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1890_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1891_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1884_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 2);
lean_ctor_set(v___x_1887_, 1, v___x_1891_);
v___x_1893_ = v___x_1887_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1884_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_a_1902_; lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1922_; 
v___x_1894_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66);
v___x_1895_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67));
lean_inc(v_currMacroScope_1881_);
lean_inc(v_quotContext_1880_);
v___x_1896_ = l_Lean_addMacroScope(v_quotContext_1880_, v___x_1895_, v_currMacroScope_1881_);
v___x_1897_ = lean_box(0);
v___x_1898_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70));
lean_inc(v_a_1884_);
v___x_1899_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1884_);
lean_ctor_set(v___x_1899_, 1, v___x_1894_);
lean_ctor_set(v___x_1899_, 2, v___x_1896_);
lean_ctor_set(v___x_1899_, 3, v___x_1898_);
lean_inc_ref(v___x_1893_);
v___x_1900_ = l_Lean_Syntax_node3(v_a_1884_, v___x_1890_, v___x_1893_, v___x_1893_, v___x_1899_);
v___x_1901_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1882_, v_a_1330_, v_a_1885_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_a_1903_ = lean_ctor_get(v___x_1901_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1922_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1922_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71));
lean_inc(v_a_1902_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 2);
lean_ctor_set(v___x_1905_, 1, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1910_ = l_Lean_Syntax_node1(v_a_1902_, v___x_1362_, v___x_1909_);
v___x_1911_ = 0;
v___x_1912_ = l_Lean_SourceInfo_fromRef(v_ref_1882_, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0));
v___x_1914_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1915_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1916_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1917_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1786_) == 1)
{
lean_object* v_val_1918_; lean_object* v___x_1919_; 
v_val_1918_ = lean_ctor_get(v___y_1786_, 0);
lean_inc(v_val_1918_);
lean_dec_ref(v___y_1786_);
v___x_1919_ = l_Array_mkArray1___redArg(v_val_1918_);
lean_inc(v_currMacroScope_1881_);
lean_inc(v_quotContext_1880_);
v___y_1365_ = v___x_1914_;
v___y_1366_ = v___x_1900_;
v___y_1367_ = v_a_1903_;
v___y_1368_ = v___x_1913_;
v___y_1369_ = v_quotContext_1880_;
v___y_1370_ = v___x_1916_;
v___y_1371_ = v_currMacroScope_1881_;
v___y_1372_ = v___x_1912_;
v___y_1373_ = v___x_1897_;
v___y_1374_ = v___x_1915_;
v___y_1375_ = v___x_1889_;
v___y_1376_ = v___x_1910_;
v___y_1377_ = v___x_1897_;
v___y_1378_ = v___x_1917_;
v___y_1379_ = v___x_1919_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1920_; 
lean_dec(v___y_1786_);
v___x_1920_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_currMacroScope_1881_);
lean_inc(v_quotContext_1880_);
v___y_1365_ = v___x_1914_;
v___y_1366_ = v___x_1900_;
v___y_1367_ = v_a_1903_;
v___y_1368_ = v___x_1913_;
v___y_1369_ = v_quotContext_1880_;
v___y_1370_ = v___x_1916_;
v___y_1371_ = v_currMacroScope_1881_;
v___y_1372_ = v___x_1912_;
v___y_1373_ = v___x_1897_;
v___y_1374_ = v___x_1915_;
v___y_1375_ = v___x_1889_;
v___y_1376_ = v___x_1910_;
v___y_1377_ = v___x_1897_;
v___y_1378_ = v___x_1917_;
v___y_1379_ = v___x_1920_;
goto v___jp_1364_;
}
}
}
}
}
}
}
}
v___jp_1332_:
{
lean_object* v_a_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1334_ = lean_ctor_get(v___y_1333_, 0);
v_a_1335_ = lean_ctor_get(v___y_1333_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___y_1333_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___y_1333_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_inc(v_a_1334_);
lean_dec(v___y_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___boxed(lean_object* v_x_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(v_x_1935_, v_a_1936_, v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1949_ = l_Lean_Parser_Tactic_optConfig;
v___x_1950_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__3));
v___x_1951_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1952_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1950_);
lean_ctor_set(v___x_1952_, 2, v___x_1949_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = l_Lean_Parser_Tactic_discharger;
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1956_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_1957_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4);
v___x_1958_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1959_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___x_1957_);
lean_ctor_set(v___x_1959_, 2, v___x_1956_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_1968_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6);
v___x_1969_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1970_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1968_);
lean_ctor_set(v___x_1970_, 2, v___x_1967_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = l_Lean_Parser_Tactic_simpLemma;
v___x_1975_ = l_Lean_Parser_Tactic_simpErase;
v___x_1976_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_1977_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
lean_ctor_set(v___x_1977_, 2, v___x_1974_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_1979_ = l_Lean_Parser_Tactic_simpStar;
v___x_1980_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_1981_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1979_);
lean_ctor_set(v___x_1981_, 2, v___x_1978_);
return v___x_1981_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18(void){
_start:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1986_ = 0;
v___x_1987_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_1988_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_1989_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__14, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14);
v___x_1990_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1988_);
lean_ctor_set(v___x_1990_, 2, v___x_1987_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v___x_1986_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__18, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18);
v___x_1992_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_1993_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_1994_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1992_);
lean_ctor_set(v___x_1994_, 2, v___x_1991_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_1998_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__19, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19);
v___x_1999_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2000_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1998_);
lean_ctor_set(v___x_2000_, 2, v___x_1997_);
return v___x_2000_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__21, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21);
v___x_2002_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2001_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2005_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10);
v___x_2006_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2007_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_2005_);
lean_ctor_set(v___x_2007_, 2, v___x_2004_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2009_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__23, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23);
v___x_2010_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2011_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
lean_ctor_set(v___x_2011_, 2, v___x_2008_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2012_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__24, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24);
v___x_2013_ = lean_unsigned_to_nat(1022u);
v___x_2014_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1));
v___x_2015_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
lean_ctor_set(v___x_2015_, 2, v___x_2012_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold(void){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__25, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
v___x_2019_ = l_String_toRawSubstring_x27(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(lean_object* v_s_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_quotContext_2025_; lean_object* v_currMacroScope_2026_; lean_object* v_ref_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_quotContext_2025_ = lean_ctor_get(v_a_2023_, 1);
v_currMacroScope_2026_ = lean_ctor_get(v_a_2023_, 2);
v_ref_2027_ = lean_ctor_get(v_a_2023_, 5);
v___x_2028_ = 0;
v___x_2029_ = l_Lean_SourceInfo_fromRef(v_ref_2027_, v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2031_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2032_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2033_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2034_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2029_, 8);
v___x_2035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2029_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2037_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2026_, 2);
lean_inc_n(v_quotContext_2025_, 2);
v___x_2038_ = l_Lean_addMacroScope(v_quotContext_2025_, v___x_2037_, v_currMacroScope_2026_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2029_);
lean_ctor_set(v___x_2040_, 1, v___x_2036_);
lean_ctor_set(v___x_2040_, 2, v___x_2038_);
lean_ctor_set(v___x_2040_, 3, v___x_2039_);
v___x_2041_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2029_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
v___x_2044_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78));
v___x_2045_ = l_Lean_addMacroScope(v_quotContext_2025_, v___x_2044_, v_currMacroScope_2026_);
v___x_2046_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82));
v___x_2047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2029_);
lean_ctor_set(v___x_2047_, 1, v___x_2043_);
lean_ctor_set(v___x_2047_, 2, v___x_2045_);
lean_ctor_set(v___x_2047_, 3, v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2029_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_Syntax_node5(v___x_2029_, v___x_2033_, v___x_2035_, v___x_2040_, v___x_2042_, v___x_2047_, v___x_2049_);
v___x_2051_ = l_Lean_Syntax_node1(v___x_2029_, v___x_2032_, v___x_2050_);
v___x_2052_ = l_Lean_Syntax_node1(v___x_2029_, v___x_2031_, v___x_2051_);
v___x_2053_ = l_Lean_Syntax_node1(v___x_2029_, v___x_2030_, v___x_2052_);
v___x_2054_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_2055_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68));
v___x_2056_ = l_Lean_Syntax_setKind(v_s_2022_, v___x_2055_);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = l_Lean_Syntax_getArg(v___x_2056_, v___x_2057_);
v___x_2059_ = 1;
v___x_2060_ = l_Lean_mkAtomFrom(v___x_2058_, v___x_2054_, v___x_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = l_Lean_Syntax_setArg(v___x_2056_, v___x_2057_, v___x_2060_);
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = l_Lean_Syntax_getArg(v___x_2061_, v___x_2062_);
v___x_2064_ = l_Lean_Parser_Tactic_appendConfig(v___x_2063_, v___x_2053_);
v___x_2065_ = l_Lean_Syntax_setArg(v___x_2061_, v___x_2062_, v___x_2064_);
v___x_2066_ = l_Lean_Syntax_mkSynthetic(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_a_2024_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3____boxed(lean_object* v_s_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(v_s_2068_, v_a_2069_, v_a_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2071_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__4(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = l_Lean_Parser_Tactic_optConfig;
v___x_2083_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__3));
v___x_2084_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2085_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__5(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2086_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2087_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__4, &l_Lean_Parser_Tactic_simpArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpArith___closed__4);
v___x_2088_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2089_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2087_);
lean_ctor_set(v___x_2089_, 2, v___x_2086_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__6(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2091_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__5, &l_Lean_Parser_Tactic_simpArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpArith___closed__5);
v___x_2092_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2093_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2091_);
lean_ctor_set(v___x_2093_, 2, v___x_2090_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__7(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2095_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__6, &l_Lean_Parser_Tactic_simpArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpArith___closed__6);
v___x_2096_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2097_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2095_);
lean_ctor_set(v___x_2097_, 2, v___x_2094_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__8(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2099_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__7, &l_Lean_Parser_Tactic_simpArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpArith___closed__7);
v___x_2100_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2101_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v___x_2098_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__9(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__8, &l_Lean_Parser_Tactic_simpArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpArith___closed__8);
v___x_2103_ = lean_unsigned_to_nat(1022u);
v___x_2104_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__1));
v___x_2105_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith(void){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__9, &l_Lean_Parser_Tactic_simpArith___closed__9_once, _init_l_Lean_Parser_Tactic_simpArith___closed__9);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__4(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = l_Lean_Parser_Tactic_optConfig;
v___x_2118_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__3));
v___x_2119_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2120_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2118_);
lean_ctor_set(v___x_2120_, 2, v___x_2117_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__5(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2122_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__4, &l_Lean_Parser_Tactic_simpArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__4);
v___x_2123_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2124_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2121_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__6(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2126_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__5, &l_Lean_Parser_Tactic_simpArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__5);
v___x_2127_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2128_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
lean_ctor_set(v___x_2128_, 2, v___x_2125_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__7(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2130_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__6, &l_Lean_Parser_Tactic_simpArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__6);
v___x_2131_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2132_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2129_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__8(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2134_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__7, &l_Lean_Parser_Tactic_simpArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__7);
v___x_2135_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2136_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2134_);
lean_ctor_set(v___x_2136_, 2, v___x_2133_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__9(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__8, &l_Lean_Parser_Tactic_simpArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__8);
v___x_2138_ = lean_unsigned_to_nat(1022u);
v___x_2139_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__1));
v___x_2140_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2138_);
lean_ctor_set(v___x_2140_, 2, v___x_2137_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang(void){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__9, &l_Lean_Parser_Tactic_simpArithBang___closed__9_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__9);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2152_ = l_Lean_Parser_Tactic_optConfig;
v___x_2153_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3));
v___x_2154_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2155_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___x_2153_);
lean_ctor_set(v___x_2155_, 2, v___x_2152_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2156_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2157_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4);
v___x_2158_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2159_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2157_);
lean_ctor_set(v___x_2159_, 2, v___x_2156_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2161_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5);
v___x_2162_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2163_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2161_);
lean_ctor_set(v___x_2163_, 2, v___x_2160_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7(void){
_start:
{
uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2164_ = 0;
v___x_2165_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_2166_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_2167_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_2168_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___x_2166_);
lean_ctor_set(v___x_2168_, 2, v___x_2165_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3, v___x_2164_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2169_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7);
v___x_2170_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_2171_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2172_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
lean_ctor_set(v___x_2172_, 2, v___x_2169_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_2174_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8);
v___x_2175_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2176_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v___x_2173_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9);
v___x_2178_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2181_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6);
v___x_2182_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2183_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2180_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11);
v___x_2185_ = lean_unsigned_to_nat(1022u);
v___x_2186_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1));
v___x_2187_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set(v___x_2187_, 2, v___x_2184_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold(void){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(lean_object* v_s_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_quotContext_2193_; lean_object* v_currMacroScope_2194_; lean_object* v_ref_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_quotContext_2193_ = lean_ctor_get(v_a_2191_, 1);
v_currMacroScope_2194_ = lean_ctor_get(v_a_2191_, 2);
v_ref_2195_ = lean_ctor_get(v_a_2191_, 5);
v___x_2196_ = 0;
v___x_2197_ = l_Lean_SourceInfo_fromRef(v_ref_2195_, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2199_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2200_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2201_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2202_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2197_, 8);
v___x_2203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2197_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2205_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2194_, 2);
lean_inc_n(v_quotContext_2193_, 2);
v___x_2206_ = l_Lean_addMacroScope(v_quotContext_2193_, v___x_2205_, v_currMacroScope_2194_);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2197_);
lean_ctor_set(v___x_2208_, 1, v___x_2204_);
lean_ctor_set(v___x_2208_, 2, v___x_2206_);
lean_ctor_set(v___x_2208_, 3, v___x_2207_);
v___x_2209_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2197_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
v___x_2212_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78));
v___x_2213_ = l_Lean_addMacroScope(v_quotContext_2193_, v___x_2212_, v_currMacroScope_2194_);
v___x_2214_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82));
v___x_2215_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2197_);
lean_ctor_set(v___x_2215_, 1, v___x_2211_);
lean_ctor_set(v___x_2215_, 2, v___x_2213_);
lean_ctor_set(v___x_2215_, 3, v___x_2214_);
v___x_2216_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2197_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = l_Lean_Syntax_node5(v___x_2197_, v___x_2201_, v___x_2203_, v___x_2208_, v___x_2210_, v___x_2215_, v___x_2217_);
v___x_2219_ = l_Lean_Syntax_node1(v___x_2197_, v___x_2200_, v___x_2218_);
v___x_2220_ = l_Lean_Syntax_node1(v___x_2197_, v___x_2199_, v___x_2219_);
v___x_2221_ = l_Lean_Syntax_node1(v___x_2197_, v___x_2198_, v___x_2220_);
v___x_2222_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61));
v___x_2223_ = l_Lean_Syntax_setKind(v_s_2190_, v___x_2222_);
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = l_Lean_Syntax_getArg(v___x_2223_, v___x_2224_);
v___x_2226_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_));
v___x_2227_ = 1;
v___x_2228_ = l_Lean_mkAtomFrom(v___x_2225_, v___x_2226_, v___x_2227_);
lean_dec(v___x_2225_);
v___x_2229_ = l_Lean_Syntax_setArg(v___x_2223_, v___x_2224_, v___x_2228_);
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = l_Lean_Syntax_getArg(v___x_2229_, v___x_2230_);
v___x_2232_ = l_Lean_Parser_Tactic_appendConfig(v___x_2231_, v___x_2221_);
v___x_2233_ = l_Lean_Syntax_setArg(v___x_2229_, v___x_2230_, v___x_2232_);
v___x_2234_ = l_Lean_Syntax_mkSynthetic(v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v_a_2192_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3____boxed(lean_object* v_s_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(v_s_2236_, v_a_2237_, v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2239_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__4(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = l_Lean_Parser_Tactic_optConfig;
v___x_2251_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__3));
v___x_2252_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2253_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
lean_ctor_set(v___x_2253_, 2, v___x_2250_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__5(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2255_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__4, &l_Lean_Parser_Tactic_simpAllArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__4);
v___x_2256_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2257_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
lean_ctor_set(v___x_2257_, 2, v___x_2254_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__6(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2258_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2259_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__5, &l_Lean_Parser_Tactic_simpAllArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__5);
v___x_2260_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2261_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2259_);
lean_ctor_set(v___x_2261_, 2, v___x_2258_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__7(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2263_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__6, &l_Lean_Parser_Tactic_simpAllArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__6);
v___x_2264_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2265_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2263_);
lean_ctor_set(v___x_2265_, 2, v___x_2262_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__8(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2266_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__7, &l_Lean_Parser_Tactic_simpAllArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__7);
v___x_2267_ = lean_unsigned_to_nat(1022u);
v___x_2268_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__1));
v___x_2269_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2267_);
lean_ctor_set(v___x_2269_, 2, v___x_2266_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith(void){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__8, &l_Lean_Parser_Tactic_simpAllArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__8);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2281_ = l_Lean_Parser_Tactic_optConfig;
v___x_2282_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__3));
v___x_2283_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2284_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v___x_2282_);
lean_ctor_set(v___x_2284_, 2, v___x_2281_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2286_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__4, &l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4);
v___x_2287_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2288_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2286_);
lean_ctor_set(v___x_2288_, 2, v___x_2285_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2290_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__5, &l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5);
v___x_2291_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2292_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2290_);
lean_ctor_set(v___x_2292_, 2, v___x_2289_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2294_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__6, &l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6);
v___x_2295_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2296_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___x_2294_);
lean_ctor_set(v___x_2296_, 2, v___x_2293_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__7, &l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7);
v___x_2298_ = lean_unsigned_to_nat(1022u);
v___x_2299_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__1));
v___x_2300_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2298_);
lean_ctor_set(v___x_2300_, 2, v___x_2297_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang(void){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__8, &l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2312_ = l_Lean_Parser_Tactic_optConfig;
v___x_2313_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3));
v___x_2314_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2315_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_2313_);
lean_ctor_set(v___x_2315_, 2, v___x_2312_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2317_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4);
v___x_2318_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2319_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2317_);
lean_ctor_set(v___x_2319_, 2, v___x_2316_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2320_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2321_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5);
v___x_2322_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2323_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___x_2321_);
lean_ctor_set(v___x_2323_, 2, v___x_2320_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2325_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6);
v___x_2326_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2327_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2324_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2329_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7);
v___x_2330_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2331_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2329_);
lean_ctor_set(v___x_2331_, 2, v___x_2328_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8);
v___x_2333_ = lean_unsigned_to_nat(1022u);
v___x_2334_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1));
v___x_2335_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2333_);
lean_ctor_set(v___x_2335_, 2, v___x_2332_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold(void){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(lean_object* v_s_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_quotContext_2340_; lean_object* v_currMacroScope_2341_; lean_object* v_ref_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_quotContext_2340_ = lean_ctor_get(v_a_2338_, 1);
v_currMacroScope_2341_ = lean_ctor_get(v_a_2338_, 2);
v_ref_2342_ = lean_ctor_get(v_a_2338_, 5);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_SourceInfo_fromRef(v_ref_2342_, v___x_2343_);
v___x_2345_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2346_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2347_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2348_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2349_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2344_, 8);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2344_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2352_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2341_, 2);
lean_inc_n(v_quotContext_2340_, 2);
v___x_2353_ = l_Lean_addMacroScope(v_quotContext_2340_, v___x_2352_, v_currMacroScope_2341_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2344_);
lean_ctor_set(v___x_2355_, 1, v___x_2351_);
lean_ctor_set(v___x_2355_, 2, v___x_2353_);
lean_ctor_set(v___x_2355_, 3, v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2344_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
v___x_2359_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78));
v___x_2360_ = l_Lean_addMacroScope(v_quotContext_2340_, v___x_2359_, v_currMacroScope_2341_);
v___x_2361_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82));
v___x_2362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2344_);
lean_ctor_set(v___x_2362_, 1, v___x_2358_);
lean_ctor_set(v___x_2362_, 2, v___x_2360_);
lean_ctor_set(v___x_2362_, 3, v___x_2361_);
v___x_2363_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2344_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_node5(v___x_2344_, v___x_2348_, v___x_2350_, v___x_2355_, v___x_2357_, v___x_2362_, v___x_2364_);
v___x_2366_ = l_Lean_Syntax_node1(v___x_2344_, v___x_2347_, v___x_2365_);
v___x_2367_ = l_Lean_Syntax_node1(v___x_2344_, v___x_2346_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v___x_2344_, v___x_2345_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_2370_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52));
v___x_2371_ = l_Lean_Syntax_setKind(v_s_2337_, v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = l_Lean_Syntax_getArg(v___x_2371_, v___x_2372_);
v___x_2374_ = 1;
v___x_2375_ = l_Lean_mkAtomFrom(v___x_2373_, v___x_2369_, v___x_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = l_Lean_Syntax_setArg(v___x_2371_, v___x_2372_, v___x_2375_);
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = l_Lean_Syntax_getArg(v___x_2376_, v___x_2377_);
v___x_2379_ = l_Lean_Parser_Tactic_appendConfig(v___x_2378_, v___x_2368_);
v___x_2380_ = l_Lean_Syntax_setArg(v___x_2376_, v___x_2377_, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_mkSynthetic(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v_a_2339_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3____boxed(lean_object* v_s_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(v_s_2383_, v_a_2384_, v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2386_;
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
