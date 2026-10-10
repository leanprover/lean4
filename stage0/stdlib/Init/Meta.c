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
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_location;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpStar;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "constructorBang"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 242, 106, 139, 253, 153, 73, 212)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 188, 57, 91, 27, 124, 155, 13)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(250, 8, 105, 97, 78, 48, 228, 109)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expandSimp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(130, 4, 119, 76, 201, 38, 241, 189)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__16_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__22_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__23_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__24_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__25_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__28_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__29_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__30_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__31_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__32 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__32_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__33_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__34_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__35 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__35_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__36_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__37 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__37_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__39_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__40_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__41 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__41_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__42_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__43_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__44 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__44_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__45_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__46_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__47 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__47_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__48_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__49_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "s.setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__50 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__50_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setKind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__52_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(10, 5, 190, 174, 53, 198, 104, 96)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "s.setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__54 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__54_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "setArg"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__56 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__56_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(51, 18, 73, 41, 18, 128, 68, 244)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__58 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__58_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__59 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__59_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__60 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__60_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__61 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__61_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__62 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__62_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__63 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__63_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__64 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__64_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__65 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__65_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkAtomFrom"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(92, 136, 63, 126, 134, 85, 56, 129)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__69 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__69_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__70 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__70_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__71 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__71_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__72 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__72_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__73 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__73_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__74 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__74_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 207, 191, 201, 123, 75, 165)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__76 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__76_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__79 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__79_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_simpAllKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__81 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__81_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__81_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__83 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__83_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "appendConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(211, 122, 231, 137, 224, 73, 76, 35)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__86 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__86_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "s.mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__87 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__87_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mkSynthetic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__89 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__89_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__89_value),LEAN_SCALAR_PTR_LITERAL(32, 59, 47, 97, 193, 185, 105, 5)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__91 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__91_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__92 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__92_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__93 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__93_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__94 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__94_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__61_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
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
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(201, 118, 35, 111, 187, 212, 189, 166)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<|>"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(15, 91, 119, 34, 57, 38, 207, 78)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ",*"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"]\""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(101, 206, 14, 113, 158, 249, 116, 159)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(228, 131, 5, 197, 58, 233, 166, 1)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_0),((lean_object*)&l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_simpAutoUnfold___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__9_value)}};
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
lean_dec_ref_known(v___x_19_, 2);
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
lean_dec_ref_known(v___x_75_, 2);
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
lean_dec_ref_known(v___x_191_, 2);
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
lean_dec_ref_known(v___x_247_, 2);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t v_sz_379_, size_t v_i_380_, lean_object* v_bs_381_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_379_ = stack[0].m_num;
size_t v_i_380_ = stack[1].m_num;
lean_object* v_bs_381_ = stack[2].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_379_, v_i_380_, v_bs_381_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0___boxed(lean_object* v_sz_391_, lean_object* v_i_392_, lean_object* v_bs_393_){
_start:
{
size_t v_sz_boxed_394_; size_t v_i_boxed_395_; lean_object* v_res_396_; 
v_sz_boxed_394_ = lean_unbox_usize(v_sz_391_);
lean_dec(v_sz_391_);
v_i_boxed_395_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_boxed_394_, v_i_boxed_395_, v_bs_393_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Array_mkArray0___redArg();
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13));
v___x_429_ = l_String_toRawSubstring_x27(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21));
v___x_443_ = l_String_toRawSubstring_x27(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(lean_object* v_x_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__2));
lean_inc(v_x_464_);
v___x_468_ = l_Lean_Syntax_isOfKind(v_x_464_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_x_464_);
v___x_469_ = lean_box(1);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_a_466_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_488_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = l_Lean_Syntax_getArg(v_x_464_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(2u);
v___x_474_ = l_Lean_Syntax_getArg(v_x_464_, v___x_473_);
v___x_536_ = lean_unsigned_to_nat(3u);
v___x_537_ = l_Lean_Syntax_getArg(v_x_464_, v___x_536_);
lean_dec(v_x_464_);
v___x_538_ = l_Lean_Syntax_getOptional_x3f(v___x_537_);
lean_dec(v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
v___y_488_ = v___x_539_;
goto v___jp_487_;
}
else
{
lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_val_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_488_ = v___x_545_;
goto v___jp_487_;
}
}
}
v___jp_475_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = l_Array_append___redArg(v___y_481_, v___y_482_);
lean_dec_ref(v___y_482_);
lean_inc(v___y_479_);
lean_inc(v___y_478_);
v___x_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_484_, 0, v___y_478_);
lean_ctor_set(v___x_484_, 1, v___y_479_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_inc(v___y_477_);
v___x_485_ = l_Lean_Syntax_node4(v___y_478_, v___y_477_, v___y_480_, v___y_476_, v___x_474_, v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_466_);
return v___x_486_;
}
v___jp_487_:
{
lean_object* v_quotContext_489_; lean_object* v_currMacroScope_490_; lean_object* v_ref_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; size_t v_sz_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_quotContext_489_ = lean_ctor_get(v_a_465_, 1);
v_currMacroScope_490_ = lean_ctor_get(v_a_465_, 2);
v_ref_491_ = lean_ctor_get(v_a_465_, 5);
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_493_ = 0;
v___x_494_ = l_Lean_SourceInfo_fromRef(v_ref_491_, v___x_493_);
v___x_495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3));
v___x_496_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4));
lean_inc_n(v___x_494_, 12);
v___x_497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_499_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
v___x_500_ = l_Lean_Parser_Tactic_getConfigItems(v___x_472_);
v_sz_501_ = lean_array_size(v___x_500_);
v___x_502_ = ((size_t)0ULL);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_501_, v___x_502_, v___x_500_);
v___x_504_ = l_Array_append___redArg(v___x_499_, v___x_503_);
lean_dec_ref(v___x_503_);
v___x_505_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_506_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_507_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_494_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14);
v___x_510_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15));
lean_inc_n(v_currMacroScope_490_, 2);
lean_inc_n(v_quotContext_489_, 2);
v___x_511_ = l_Lean_addMacroScope(v_quotContext_489_, v___x_510_, v_currMacroScope_490_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_494_);
lean_ctor_set(v___x_513_, 1, v___x_509_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
lean_ctor_set(v___x_513_, 3, v___x_512_);
v___x_514_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_494_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19));
v___x_517_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20));
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_494_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22);
v___x_520_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23));
v___x_521_ = l_Lean_addMacroScope(v_quotContext_489_, v___x_520_, v_currMacroScope_490_);
v___x_522_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29));
v___x_523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_523_, 0, v___x_494_);
lean_ctor_set(v___x_523_, 1, v___x_519_);
lean_ctor_set(v___x_523_, 2, v___x_521_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
v___x_524_ = l_Lean_Syntax_node2(v___x_494_, v___x_516_, v___x_518_, v___x_523_);
v___x_525_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_494_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Syntax_node5(v___x_494_, v___x_506_, v___x_508_, v___x_513_, v___x_515_, v___x_524_, v___x_526_);
v___x_528_ = l_Lean_Syntax_node1(v___x_494_, v___x_505_, v___x_527_);
v___x_529_ = lean_array_push(v___x_504_, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_530_, 0, v___x_494_);
lean_ctor_set(v___x_530_, 1, v___x_498_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
v___x_531_ = l_Lean_Syntax_node1(v___x_494_, v___x_492_, v___x_530_);
if (lean_obj_tag(v___y_488_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___y_476_ = v___x_531_;
v___y_477_ = v___x_495_;
v___y_478_ = v___x_494_;
v___y_479_ = v___x_498_;
v___y_480_ = v___x_497_;
v___y_481_ = v___x_499_;
v___y_482_ = v___x_532_;
goto v___jp_475_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_val_533_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___y_488_, 1);
v___x_534_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
v___x_535_ = lean_array_push(v___x_534_, v_val_533_);
v___y_476_ = v___x_531_;
v___y_477_ = v___x_495_;
v___y_478_ = v___x_494_;
v___y_479_ = v___x_498_;
v___y_480_ = v___x_497_;
v___y_481_ = v___x_499_;
v___y_482_ = v___x_535_;
goto v___jp_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___boxed(lean_object* v_x_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(v_x_548_, v_a_549_, v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__7));
v___x_573_ = l_String_toRawSubstring_x27(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1(lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__1));
lean_inc(v_x_587_);
v___x_591_ = l_Lean_Syntax_isOfKind(v_x_587_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_x_587_);
v___x_592_ = lean_box(1);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_a_589_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = l_Lean_Syntax_getArg(v_x_587_, v___x_594_);
lean_dec(v_x_587_);
v___x_596_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
lean_inc(v___x_595_);
v___x_597_ = l_Lean_Syntax_isOfKind(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_595_);
v___x_598_ = lean_box(1);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_a_589_);
return v___x_599_;
}
else
{
lean_object* v_quotContext_600_; lean_object* v_currMacroScope_601_; lean_object* v_ref_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; size_t v_sz_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_quotContext_600_ = lean_ctor_get(v_a_588_, 1);
v_currMacroScope_601_ = lean_ctor_get(v_a_588_, 2);
v_ref_602_ = lean_ctor_get(v_a_588_, 5);
v___x_603_ = 0;
v___x_604_ = l_Lean_SourceInfo_fromRef(v_ref_602_, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__2));
v___x_606_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__3));
lean_inc_n(v___x_604_, 7);
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_604_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
v___x_608_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_609_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
v___x_610_ = l_Lean_Parser_Tactic_getConfigItems(v___x_595_);
v_sz_611_ = lean_array_size(v___x_610_);
v___x_612_ = ((size_t)0ULL);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_611_, v___x_612_, v___x_610_);
v___x_614_ = l_Array_append___redArg(v___x_609_, v___x_613_);
lean_dec_ref(v___x_613_);
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_616_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__5));
v___x_617_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__6));
v___x_618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_604_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__8);
v___x_620_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__9));
lean_inc(v_currMacroScope_601_);
lean_inc(v_quotContext_600_);
v___x_621_ = l_Lean_addMacroScope(v_quotContext_600_, v___x_620_, v_currMacroScope_601_);
v___x_622_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___closed__12));
v___x_623_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_623_, 0, v___x_604_);
lean_ctor_set(v___x_623_, 1, v___x_619_);
lean_ctor_set(v___x_623_, 2, v___x_621_);
lean_ctor_set(v___x_623_, 3, v___x_622_);
v___x_624_ = l_Lean_Syntax_node2(v___x_604_, v___x_616_, v___x_618_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node1(v___x_604_, v___x_615_, v___x_624_);
v___x_626_ = lean_array_push(v___x_614_, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_627_, 0, v___x_604_);
lean_ctor_set(v___x_627_, 1, v___x_608_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
v___x_628_ = l_Lean_Syntax_node1(v___x_604_, v___x_596_, v___x_627_);
v___x_629_ = l_Lean_Syntax_node2(v___x_604_, v___x_606_, v___x_607_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_a_589_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1___boxed(lean_object* v_x_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__constructorBang__1(v_x_631_, v_a_632_, v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_794_ = l_Lean_Parser_Tactic_optConfig;
v___x_795_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30));
v___x_796_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_797_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
lean_ctor_set(v___x_797_, 2, v___x_794_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31);
v___x_799_ = lean_unsigned_to_nat(1022u);
v___x_800_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
v___x_801_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
lean_ctor_set(v___x_801_, 2, v___x_798_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_declareSimpLikeTactic(void){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_obj_once(&l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32, &l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once, _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(lean_object* v_____do__lift_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = 0;
v___x_807_ = l_Lean_SourceInfo_fromRef(v_____do__lift_803_, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___y_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0___boxed(lean_object* v_____do__lift_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_____do__lift_809_, v___y_810_, v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v_____do__lift_809_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__14));
v___x_829_ = l_String_toRawSubstring_x27(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20));
v___x_837_ = l_String_toRawSubstring_x27(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__26));
v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__37));
v___x_858_ = l_String_toRawSubstring_x27(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__50));
v___x_873_ = l_String_toRawSubstring_x27(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__54));
v___x_880_ = l_String_toRawSubstring_x27(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__65));
v___x_896_ = l_String_toRawSubstring_x27(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67));
v___x_899_ = l_String_toRawSubstring_x27(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__74));
v___x_909_ = l_String_toRawSubstring_x27(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__13));
v___x_913_ = l_String_toRawSubstring_x27(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84));
v___x_929_ = l_String_toRawSubstring_x27(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__87));
v___x_934_ = l_String_toRawSubstring_x27(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(lean_object* v___x_943_, lean_object* v___x_944_, lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v___x_948_, lean_object* v___x_949_, lean_object* v___x_950_, lean_object* v_____x_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_snd_954_; lean_object* v_fst_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1225_; 
v_snd_954_ = lean_ctor_get(v_____x_951_, 1);
v_fst_955_ = lean_ctor_get(v_____x_951_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_____x_951_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_957_ = v_____x_951_;
v_isShared_958_ = v_isSharedCheck_1225_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_954_);
lean_inc(v_fst_955_);
lean_dec(v_____x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1225_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1224_; 
v_fst_959_ = lean_ctor_get(v_snd_954_, 0);
v_snd_960_ = lean_ctor_get(v_snd_954_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_snd_954_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_962_ = v_snd_954_;
v_isShared_963_ = v_isSharedCheck_1224_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_snd_960_);
lean_inc(v_fst_959_);
lean_dec(v_snd_954_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1224_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_quotContext_964_; lean_object* v_currMacroScope_965_; lean_object* v_ref_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v_quotContext_964_ = lean_ctor_get(v___y_952_, 1);
v_currMacroScope_965_ = lean_ctor_get(v___y_952_, 2);
v_ref_966_ = lean_ctor_get(v___y_952_, 5);
v___x_967_ = 0;
v___x_968_ = l_Lean_SourceInfo_fromRef(v_ref_966_, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_970_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0));
v___x_971_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__1));
lean_inc_ref_n(v___x_944_, 3);
lean_inc_ref_n(v___x_943_, 3);
v___x_972_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__2));
v___x_974_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_973_);
v___x_975_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
lean_inc_n(v___x_968_, 2);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_968_);
lean_ctor_set(v___x_976_, 1, v___x_969_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_978_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__3));
v___x_979_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__4));
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 2);
lean_ctor_set(v___x_962_, 1, v___x_980_);
lean_ctor_set(v___x_962_, 0, v___x_968_);
v___x_982_ = v___x_962_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_1223_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_983_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__5));
lean_inc_ref_n(v___x_944_, 3);
lean_inc_ref_n(v___x_943_, 3);
v___x_984_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6));
v___x_986_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_985_);
lean_inc_ref(v___x_976_);
lean_inc_n(v___x_968_, 2);
v___x_987_ = l_Lean_Syntax_node1(v___x_968_, v___x_986_, v___x_976_);
v___x_988_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__7));
v___x_989_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__8));
v___x_990_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_988_, v___x_989_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 2);
lean_ctor_set(v___x_957_, 1, v___x_989_);
lean_ctor_set(v___x_957_, 0, v___x_968_);
v___x_992_ = v___x_957_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_989_);
v___x_992_ = v_reuseFailAlloc_1222_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_inc_n(v___x_968_, 97);
v___x_993_ = l_Lean_Syntax_node2(v___x_968_, v___x_990_, v___x_992_, v___x_945_);
v___x_994_ = l_Lean_Syntax_node2(v___x_968_, v___x_984_, v___x_987_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__9));
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_968_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_inc_ref_n(v___x_997_, 2);
v___x_998_ = l_Lean_Syntax_node3(v___x_968_, v___x_979_, v___x_982_, v___x_995_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__10));
lean_inc_ref_n(v___x_944_, 27);
lean_inc_ref_n(v___x_943_, 29);
v___x_1001_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_968_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_968_, v___x_1001_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v___x_1003_);
lean_inc_ref_n(v___x_976_, 32);
v___x_1005_ = l_Lean_Syntax_node7(v___x_968_, v___x_974_, v___x_976_, v___x_999_, v___x_976_, v___x_976_, v___x_1004_, v___x_976_, v___x_976_);
v___x_1006_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__11));
v___x_1007_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__12));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_968_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__13));
v___x_1011_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__15);
v___x_1013_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__16));
lean_inc_n(v_currMacroScope_965_, 13);
lean_inc_n(v_quotContext_964_, 13);
v___x_1014_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1013_, v_currMacroScope_965_);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1016_, 0, v___x_968_);
lean_ctor_set(v___x_1016_, 1, v___x_1012_);
lean_ctor_set(v___x_1016_, 2, v___x_1014_);
lean_ctor_set(v___x_1016_, 3, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_968_, v___x_1011_, v___x_1016_, v___x_976_);
v___x_1018_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__17));
v___x_1019_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__18));
v___x_1021_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19));
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_968_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__20));
v___x_1025_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__21);
v___x_1026_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__22));
v___x_1027_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1026_, v_currMacroScope_965_);
v___x_1028_ = l_Lean_Name_mkStr2(v___x_943_, v___x_1024_);
lean_inc(v___x_1028_);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1015_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1015_);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1033_, 0, v___x_968_);
lean_ctor_set(v___x_1033_, 1, v___x_1025_);
lean_ctor_set(v___x_1033_, 2, v___x_1027_);
lean_ctor_set(v___x_1033_, 3, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node2(v___x_968_, v___x_1021_, v___x_1023_, v___x_1033_);
v___x_1035_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v___x_1034_);
v___x_1036_ = l_Lean_Syntax_node2(v___x_968_, v___x_1019_, v___x_976_, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__23));
v___x_1038_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_970_, v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_968_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__24));
v___x_1042_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_968_);
lean_ctor_set(v___x_1043_, 1, v___x_1041_);
v___x_1044_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__25));
v___x_1045_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__27);
v___x_1047_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__28));
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1047_, v_currMacroScope_965_);
v___x_1049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1049_, 0, v___x_968_);
lean_ctor_set(v___x_1049_, 1, v___x_1046_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
lean_ctor_set(v___x_1049_, 3, v___x_1015_);
lean_inc_ref_n(v___x_1049_, 3);
v___x_1050_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__29));
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_968_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__30));
v___x_1054_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_968_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__31));
v___x_1057_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__32));
v___x_1059_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__33));
v___x_1061_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__34));
v___x_1063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_968_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__35));
v___x_1065_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node1(v___x_968_, v___x_1065_, v___x_976_);
v___x_1067_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__36));
v___x_1068_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__38);
v___x_1070_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__39));
v___x_1071_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1070_, v_currMacroScope_965_);
v___x_1072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1072_, 0, v___x_968_);
lean_ctor_set(v___x_1072_, 1, v___x_1069_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
lean_ctor_set(v___x_1072_, 3, v___x_1015_);
v___x_1073_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__40));
v___x_1074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_968_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__41));
v___x_1076_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__42));
v___x_1078_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__43));
v___x_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_968_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_inc_ref(v___x_946_);
v___x_1081_ = l_String_toRawSubstring_x27(v___x_946_);
v___x_1082_ = l_Lean_Name_mkStr1(v___x_946_);
v___x_1083_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1082_, v_currMacroScope_965_);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_947_);
lean_ctor_set(v___x_1084_, 1, v___x_1015_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v___x_1015_);
v___x_1086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1086_, 0, v___x_968_);
lean_ctor_set(v___x_1086_, 1, v___x_1081_);
lean_ctor_set(v___x_1086_, 2, v___x_1083_);
lean_ctor_set(v___x_1086_, 3, v___x_1085_);
v___x_1087_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__44));
v___x_1088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_968_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_968_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_inc_ref_n(v___x_1090_, 3);
v___x_1091_ = l_Lean_Syntax_node5(v___x_968_, v___x_1078_, v___x_1080_, v___x_1086_, v___x_1088_, v___x_948_, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node1(v___x_968_, v___x_1076_, v___x_1091_);
lean_inc_ref(v___x_1072_);
v___x_1093_ = l_Lean_Syntax_node4(v___x_968_, v___x_1068_, v___x_1072_, v___x_976_, v___x_1074_, v___x_1092_);
lean_inc_n(v___x_1066_, 4);
lean_inc_ref_n(v___x_1063_, 4);
v___x_1094_ = l_Lean_Syntax_node4(v___x_968_, v___x_1061_, v___x_1063_, v___x_976_, v___x_1066_, v___x_1093_);
lean_inc_n(v___x_1059_, 5);
v___x_1095_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1094_, v___x_976_);
v___x_1096_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__45));
v___x_1097_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__46));
v___x_1099_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__47));
v___x_1101_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1100_);
v___x_1102_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__48));
v___x_1103_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1102_);
v___x_1104_ = l_Lean_Syntax_node1(v___x_968_, v___x_1103_, v___x_1049_);
v___x_1105_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__49));
v___x_1106_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1105_);
v___x_1107_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__51);
v___x_1108_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__53));
v___x_1109_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1108_, v_currMacroScope_965_);
v___x_1110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1110_, 0, v___x_968_);
lean_ctor_set(v___x_1110_, 1, v___x_1107_);
lean_ctor_set(v___x_1110_, 2, v___x_1109_);
lean_ctor_set(v___x_1110_, 3, v___x_1015_);
v___x_1111_ = l_Lean_Syntax_node1(v___x_968_, v___x_969_, v_fst_955_);
lean_inc_n(v___x_1106_, 4);
v___x_1112_ = l_Lean_Syntax_node2(v___x_968_, v___x_1106_, v___x_1110_, v___x_1111_);
lean_inc_ref_n(v___x_1040_, 5);
lean_inc_n(v___x_1104_, 3);
lean_inc_n(v___x_1101_, 3);
v___x_1113_ = l_Lean_Syntax_node5(v___x_968_, v___x_1101_, v___x_1104_, v___x_976_, v___x_976_, v___x_1040_, v___x_1112_);
lean_inc_n(v___x_1099_, 3);
v___x_1114_ = l_Lean_Syntax_node1(v___x_968_, v___x_1099_, v___x_1113_);
lean_inc_n(v___x_1097_, 3);
v___x_1115_ = l_Lean_Syntax_node4(v___x_968_, v___x_1097_, v___x_1063_, v___x_976_, v___x_1066_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1115_, v___x_976_);
v___x_1117_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__55);
v___x_1118_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__57));
v___x_1119_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1118_, v_currMacroScope_965_);
v___x_1120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1120_, 0, v___x_968_);
lean_ctor_set(v___x_1120_, 1, v___x_1117_);
lean_ctor_set(v___x_1120_, 2, v___x_1119_);
lean_ctor_set(v___x_1120_, 3, v___x_1015_);
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__59));
v___x_1122_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__60));
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_968_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node1(v___x_968_, v___x_1121_, v___x_1123_);
v___x_1125_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__61));
v___x_1126_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1125_);
v___x_1127_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__62));
v___x_1128_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_968_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__64));
v___x_1132_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__66);
v___x_1133_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_949_, v_currMacroScope_965_);
lean_inc_ref(v___x_950_);
v___x_1134_ = l_Lean_Name_mkStr3(v___x_943_, v___x_944_, v___x_950_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1015_);
v___x_1137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1137_, 0, v___x_968_);
lean_ctor_set(v___x_1137_, 1, v___x_1132_);
lean_ctor_set(v___x_1137_, 2, v___x_1133_);
lean_ctor_set(v___x_1137_, 3, v___x_1136_);
v___x_1138_ = l_Lean_Syntax_node1(v___x_968_, v___x_1131_, v___x_1137_);
lean_inc_ref(v___x_1130_);
v___x_1139_ = l_Lean_Syntax_node2(v___x_968_, v___x_1128_, v___x_1130_, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__67));
v___x_1141_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__68);
v___x_1142_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__69));
v___x_1143_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1142_, v_currMacroScope_965_);
v___x_1144_ = l_Lean_Name_mkStr2(v___x_943_, v___x_1140_);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1015_);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1015_);
v___x_1147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1147_, 0, v___x_968_);
lean_ctor_set(v___x_1147_, 1, v___x_1141_);
lean_ctor_set(v___x_1147_, 2, v___x_1143_);
lean_ctor_set(v___x_1147_, 3, v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__71));
v___x_1149_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__72));
v___x_1150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_968_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
lean_inc(v___x_1124_);
lean_inc_ref(v___x_1150_);
v___x_1151_ = l_Lean_Syntax_node4(v___x_968_, v___x_1148_, v___x_1049_, v___x_1150_, v___x_1124_, v___x_997_);
v___x_1152_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__73));
v___x_1153_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__75);
v___x_1155_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__76));
v___x_1156_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1155_, v_currMacroScope_965_);
v___x_1157_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1157_, 0, v___x_968_);
lean_ctor_set(v___x_1157_, 1, v___x_1154_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_ctor_set(v___x_1157_, 3, v___x_1015_);
v___x_1158_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77);
v___x_1159_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78));
v___x_1160_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1159_, v_currMacroScope_965_);
v___x_1161_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82));
v___x_1162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1162_, 0, v___x_968_);
lean_ctor_set(v___x_1162_, 1, v___x_1158_);
lean_ctor_set(v___x_1162_, 2, v___x_1160_);
lean_ctor_set(v___x_1162_, 3, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_node5(v___x_968_, v___x_1153_, v___x_1130_, v___x_1157_, v___x_1040_, v___x_1162_, v___x_1090_);
v___x_1164_ = l_Lean_Syntax_node3(v___x_968_, v___x_969_, v___x_1151_, v_fst_959_, v___x_1163_);
v___x_1165_ = l_Lean_Syntax_node2(v___x_968_, v___x_1106_, v___x_1147_, v___x_1164_);
lean_inc(v___x_1139_);
lean_inc(v___x_1126_);
v___x_1166_ = l_Lean_Syntax_node3(v___x_968_, v___x_1126_, v___x_1139_, v___x_1165_, v___x_1090_);
v___x_1167_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_1124_, v___x_1166_);
lean_inc_ref(v___x_1120_);
v___x_1168_ = l_Lean_Syntax_node2(v___x_968_, v___x_1106_, v___x_1120_, v___x_1167_);
v___x_1169_ = l_Lean_Syntax_node5(v___x_968_, v___x_1101_, v___x_1104_, v___x_976_, v___x_976_, v___x_1040_, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node1(v___x_968_, v___x_1099_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node4(v___x_968_, v___x_1097_, v___x_1063_, v___x_976_, v___x_1066_, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1171_, v___x_976_);
v___x_1173_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__83));
v___x_1174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_968_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_node1(v___x_968_, v___x_1121_, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__84));
v___x_1177_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__85);
v___x_1178_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__86));
v___x_1179_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1178_, v_currMacroScope_965_);
v___x_1180_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_950_, v___x_1176_);
v___x_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1015_);
v___x_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1015_);
v___x_1183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1183_, 0, v___x_968_);
lean_ctor_set(v___x_1183_, 1, v___x_1177_);
lean_ctor_set(v___x_1183_, 2, v___x_1179_);
lean_ctor_set(v___x_1183_, 3, v___x_1182_);
lean_inc(v___x_1175_);
v___x_1184_ = l_Lean_Syntax_node4(v___x_968_, v___x_1148_, v___x_1049_, v___x_1150_, v___x_1175_, v___x_997_);
v___x_1185_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_1184_, v___x_1072_);
v___x_1186_ = l_Lean_Syntax_node2(v___x_968_, v___x_1106_, v___x_1183_, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_node3(v___x_968_, v___x_1126_, v___x_1139_, v___x_1186_, v___x_1090_);
v___x_1188_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_1175_, v___x_1187_);
v___x_1189_ = l_Lean_Syntax_node2(v___x_968_, v___x_1106_, v___x_1120_, v___x_1188_);
v___x_1190_ = l_Lean_Syntax_node5(v___x_968_, v___x_1101_, v___x_1104_, v___x_976_, v___x_976_, v___x_1040_, v___x_1189_);
v___x_1191_ = l_Lean_Syntax_node1(v___x_968_, v___x_1099_, v___x_1190_);
v___x_1192_ = l_Lean_Syntax_node4(v___x_968_, v___x_1097_, v___x_1063_, v___x_976_, v___x_1066_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1192_, v___x_976_);
v___x_1194_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__88);
v___x_1195_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__90));
v___x_1196_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_1195_, v_currMacroScope_965_);
v___x_1197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1197_, 0, v___x_968_);
lean_ctor_set(v___x_1197_, 1, v___x_1194_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
lean_ctor_set(v___x_1197_, 3, v___x_1015_);
v___x_1198_ = l_Lean_Syntax_node5(v___x_968_, v___x_1101_, v___x_1104_, v___x_976_, v___x_976_, v___x_1040_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_node1(v___x_968_, v___x_1099_, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node4(v___x_968_, v___x_1097_, v___x_1063_, v___x_976_, v___x_1066_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1200_, v___x_976_);
v___x_1202_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__91));
v___x_1203_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_977_, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__92));
v___x_1205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_968_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
lean_inc(v___x_1050_);
v___x_1206_ = l_Lean_Syntax_node2(v___x_968_, v___x_1203_, v___x_1205_, v___x_1050_);
v___x_1207_ = l_Lean_Syntax_node2(v___x_968_, v___x_1059_, v___x_1206_, v___x_976_);
v___x_1208_ = l_Lean_Syntax_node6(v___x_968_, v___x_969_, v___x_1095_, v___x_1116_, v___x_1172_, v___x_1193_, v___x_1201_, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node1(v___x_968_, v___x_1057_, v___x_1208_);
v___x_1210_ = l_Lean_Syntax_node2(v___x_968_, v___x_1054_, v___x_1055_, v___x_1209_);
v___x_1211_ = l_Lean_Syntax_node4(v___x_968_, v___x_1045_, v___x_1050_, v___x_976_, v___x_1052_, v___x_1210_);
v___x_1212_ = l_Lean_Syntax_node2(v___x_968_, v___x_1042_, v___x_1043_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__93));
v___x_1214_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__94));
v___x_1215_ = l_Lean_Name_mkStr4(v___x_943_, v___x_944_, v___x_1213_, v___x_1214_);
v___x_1216_ = l_Lean_Syntax_node2(v___x_968_, v___x_1215_, v___x_976_, v___x_976_);
v___x_1217_ = l_Lean_Syntax_node4(v___x_968_, v___x_1038_, v___x_1040_, v___x_1212_, v___x_1216_, v___x_976_);
v___x_1218_ = l_Lean_Syntax_node5(v___x_968_, v___x_1007_, v___x_1009_, v___x_1017_, v___x_1036_, v___x_1217_, v___x_976_);
v___x_1219_ = l_Lean_Syntax_node2(v___x_968_, v___x_972_, v___x_1005_, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v_snd_960_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___y_953_);
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v___x_1233_, lean_object* v_____x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1226_, v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_, v___x_1231_, v___x_1232_, v___x_1233_, v_____x_1234_, v___y_1235_, v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1237_;
}
}
lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(uint8_t v___x_1238_, lean_object* v_____do__lift_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1239_, v___x_1238_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___y_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1238_ = stack[0].m_num;
lean_object* v_____do__lift_1239_ = stack[1].m_obj;
lean_object* v___y_1240_ = stack[2].m_obj;
lean_object* v___y_1241_ = stack[3].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1238_, v_____do__lift_1239_, v___y_1240_, v___y_1241_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___boxed(lean_object* v___x_1245_, lean_object* v_____do__lift_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___x_35752__boxed_1249_; lean_object* v_res_1250_; 
v___x_35752__boxed_1249_ = lean_unbox(v___x_1245_);
v_res_1250_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_35752__boxed_1249_, v_____do__lift_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v_____do__lift_1246_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1266_ = l_String_toRawSubstring_x27(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11));
v___x_1279_ = l_String_toRawSubstring_x27(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25));
v___x_1305_ = l_String_toRawSubstring_x27(v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30));
v___x_1316_ = l_String_toRawSubstring_x27(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36));
v___x_1328_ = l_String_toRawSubstring_x27(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39));
v___x_1333_ = l_String_toRawSubstring_x27(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43));
v___x_1343_ = l_String_toRawSubstring_x27(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_1359_ = l_String_toRawSubstring_x27(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58));
v___x_1382_ = l_String_toRawSubstring_x27(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_1399_ = l_String_toRawSubstring_x27(v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(lean_object* v_x_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___y_1418_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1428_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0));
v___x_1429_ = ((lean_object*)(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1));
v___x_1430_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__0));
v___x_1431_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1));
lean_inc(v_x_1414_);
v___x_1432_ = l_Lean_Syntax_isOfKind(v_x_1414_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_x_1414_);
v___x_1433_ = lean_box(1);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_a_1416_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1871_; lean_object* v___x_2010_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1435_);
v___x_1437_ = lean_unsigned_to_nat(2u);
v___x_1438_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1437_);
v___x_1439_ = lean_unsigned_to_nat(4u);
v___x_1440_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(6u);
v___x_1442_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1441_);
v___x_1443_ = lean_unsigned_to_nat(8u);
v___x_1444_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1443_);
lean_dec(v_x_1414_);
v___x_1445_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0));
v___x_1446_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_1447_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27));
v___x_1448_ = lean_box(0);
v___x_2010_ = l_Lean_Syntax_getOptional_x3f(v___x_1436_);
lean_dec(v___x_1436_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
v___y_1871_ = v___x_2011_;
goto v___jp_1870_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_val_2012_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v___y_1871_ = v___x_2017_;
goto v___jp_1870_;
}
}
}
v___jp_1449_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_inc_ref_n(v___y_1451_, 2);
v___x_1465_ = l_Array_append___redArg(v___y_1451_, v___y_1464_);
lean_dec_ref(v___y_1464_);
lean_inc_n(v___y_1461_, 8);
lean_inc_n(v___y_1457_, 48);
v___x_1466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1457_);
lean_ctor_set(v___x_1466_, 1, v___y_1461_);
lean_ctor_set(v___x_1466_, 2, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1457_);
lean_ctor_set(v___x_1467_, 1, v___y_1461_);
lean_ctor_set(v___x_1467_, 2, v___y_1451_);
v___x_1468_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6));
lean_inc_ref(v___y_1459_);
v___x_1469_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1459_, v___x_1468_);
lean_inc_ref_n(v___x_1467_, 7);
v___x_1470_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1469_, v___x_1467_);
lean_inc_ref(v___y_1454_);
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1457_);
lean_ctor_set(v___x_1471_, 1, v___y_1454_);
v___x_1472_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1458_);
v___x_1473_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1458_, v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1457_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___y_1457_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___y_1457_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1457_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc_ref_n(v___x_1481_, 4);
lean_inc(v___x_1440_);
lean_inc_ref_n(v___x_1475_, 4);
v___x_1482_ = l_Lean_Syntax_node5(v___y_1457_, v___x_1473_, v___x_1475_, v___x_1477_, v___x_1479_, v___x_1440_, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_node1(v___y_1457_, v___y_1461_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1485_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1484_, v___x_1442_);
v___x_1486_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1487_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1488_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1452_, 4);
lean_inc_n(v___y_1463_, 4);
v___x_1489_ = l_Lean_addMacroScope(v___y_1463_, v___x_1488_, v___y_1452_);
lean_inc_n(v___y_1455_, 4);
v___x_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1446_);
lean_ctor_set(v___x_1490_, 1, v___y_1455_);
lean_inc_n(v___y_1462_, 5);
v___x_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___y_1462_);
v___x_1492_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1457_);
lean_ctor_set(v___x_1492_, 1, v___x_1487_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
lean_ctor_set(v___x_1492_, 3, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1486_, v___x_1492_, v___x_1467_);
v___x_1494_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1495_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1496_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1497_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1498_ = l_Lean_addMacroScope(v___y_1463_, v___x_1497_, v___y_1452_);
v___x_1499_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___y_1455_);
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___y_1462_);
v___x_1502_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1457_);
lean_ctor_set(v___x_1502_, 1, v___x_1496_);
lean_ctor_set(v___x_1502_, 2, v___x_1498_);
lean_ctor_set(v___x_1502_, 3, v___x_1501_);
v___x_1503_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1486_, v___x_1502_, v___x_1467_);
v___x_1504_ = l_Lean_Syntax_node1(v___y_1457_, v___y_1461_, v___x_1503_);
v___x_1505_ = l_Lean_Syntax_node3(v___y_1457_, v___x_1495_, v___x_1475_, v___x_1504_, v___x_1481_);
v___x_1506_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1457_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
lean_inc_ref_n(v___x_1507_, 2);
v___x_1508_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1494_, v___x_1505_, v___x_1507_);
v___x_1509_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1510_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___y_1457_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___y_1457_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1447_, v___x_1513_);
v___x_1515_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1509_, v___x_1511_, v___x_1514_);
v___x_1516_ = l_Lean_Syntax_node1(v___y_1457_, v___y_1461_, v___x_1515_);
v___x_1517_ = l_Lean_Syntax_node3(v___y_1457_, v___x_1495_, v___x_1475_, v___x_1516_, v___x_1481_);
v___x_1518_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1494_, v___x_1517_, v___x_1507_);
v___x_1519_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___y_1457_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1447_, v___x_1520_);
v___x_1522_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1484_, v___x_1521_);
v___x_1523_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1524_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1525_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
v___x_1526_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27));
v___x_1527_ = l_Lean_addMacroScope(v___y_1463_, v___x_1526_, v___y_1452_);
v___x_1528_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28));
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___y_1455_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___y_1462_);
v___x_1531_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1531_, 0, v___y_1457_);
lean_ctor_set(v___x_1531_, 1, v___x_1525_);
lean_ctor_set(v___x_1531_, 2, v___x_1527_);
lean_ctor_set(v___x_1531_, 3, v___x_1530_);
v___x_1532_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1486_, v___x_1531_, v___x_1467_);
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1457_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1536_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1537_ = l_Lean_addMacroScope(v___y_1463_, v___x_1536_, v___y_1452_);
v___x_1538_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___y_1455_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___y_1462_);
v___x_1541_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1541_, 0, v___y_1457_);
lean_ctor_set(v___x_1541_, 1, v___x_1535_);
lean_ctor_set(v___x_1541_, 2, v___x_1537_);
lean_ctor_set(v___x_1541_, 3, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1486_, v___x_1541_, v___x_1467_);
v___x_1543_ = l_Lean_Syntax_node3(v___y_1457_, v___x_1524_, v___x_1532_, v___x_1534_, v___x_1542_);
v___x_1544_ = l_Lean_Syntax_node1(v___y_1457_, v___y_1461_, v___x_1543_);
v___x_1545_ = l_Lean_Syntax_node3(v___y_1457_, v___x_1495_, v___x_1475_, v___x_1544_, v___x_1481_);
v___x_1546_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34));
v___x_1547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___y_1457_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1523_, v___x_1545_, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35));
v___x_1550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___y_1457_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1447_, v___x_1550_);
v___x_1552_ = l_Lean_Syntax_node1(v___y_1457_, v___x_1484_, v___x_1551_);
v___x_1553_ = l_Lean_Syntax_node3(v___y_1457_, v___y_1461_, v___x_1522_, v___x_1548_, v___x_1552_);
v___x_1554_ = l_Lean_Syntax_node3(v___y_1457_, v___x_1495_, v___x_1475_, v___x_1553_, v___x_1481_);
v___x_1555_ = l_Lean_Syntax_node2(v___y_1457_, v___x_1494_, v___x_1554_, v___x_1507_);
v___x_1556_ = l_Lean_Syntax_node5(v___y_1457_, v___y_1461_, v___x_1485_, v___x_1493_, v___x_1508_, v___x_1518_, v___x_1555_);
v___x_1557_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19));
v___x_1558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1457_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37);
v___x_1560_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1561_ = l_Lean_addMacroScope(v___y_1463_, v___x_1560_, v___y_1452_);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v___y_1457_);
lean_ctor_set(v___x_1562_, 1, v___x_1559_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
lean_ctor_set(v___x_1562_, 3, v___y_1462_);
v___x_1563_ = lean_unsigned_to_nat(10u);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
v___x_1565_ = lean_array_push(v___x_1564_, v___x_1466_);
v___x_1566_ = lean_array_push(v___x_1565_, v___x_1467_);
v___x_1567_ = lean_array_push(v___x_1566_, v___x_1470_);
v___x_1568_ = lean_array_push(v___x_1567_, v___x_1471_);
v___x_1569_ = lean_array_push(v___x_1568_, v___x_1467_);
v___x_1570_ = lean_array_push(v___x_1569_, v___x_1483_);
v___x_1571_ = lean_array_push(v___x_1570_, v___x_1467_);
v___x_1572_ = lean_array_push(v___x_1571_, v___x_1556_);
v___x_1573_ = lean_array_push(v___x_1572_, v___x_1558_);
v___x_1574_ = lean_array_push(v___x_1573_, v___x_1562_);
lean_inc(v___y_1456_);
v___x_1575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1575_, 0, v___y_1457_);
lean_ctor_set(v___x_1575_, 1, v___y_1456_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___y_1460_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1453_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1428_, v___x_1429_, v___x_1440_, v___x_1445_, v___x_1446_, v___x_1444_, v___x_1448_, v___x_1430_, v___x_1577_, v_a_1415_, v___y_1450_);
v___y_1418_ = v___x_1578_;
goto v___jp_1417_;
}
v___jp_1579_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc_ref_n(v___y_1586_, 2);
v___x_1595_ = l_Array_append___redArg(v___y_1586_, v___y_1594_);
lean_dec_ref(v___y_1594_);
lean_inc_n(v___y_1587_, 9);
lean_inc_n(v___y_1583_, 53);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1583_);
lean_ctor_set(v___x_1596_, 1, v___y_1587_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___y_1583_);
lean_ctor_set(v___x_1597_, 1, v___y_1587_);
lean_ctor_set(v___x_1597_, 2, v___y_1586_);
v___x_1598_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6));
lean_inc_ref(v___y_1588_);
v___x_1599_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1588_, v___x_1598_);
lean_inc_ref_n(v___x_1597_, 8);
v___x_1600_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1599_, v___x_1597_);
lean_inc_ref(v___y_1590_);
v___x_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___y_1583_);
lean_ctor_set(v___x_1601_, 1, v___y_1590_);
v___x_1602_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1591_);
v___x_1603_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1591_, v___x_1602_);
v___x_1604_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1583_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___y_1583_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___y_1583_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1583_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc_ref_n(v___x_1611_, 5);
lean_inc(v___x_1440_);
lean_inc_ref_n(v___x_1605_, 5);
v___x_1612_ = l_Lean_Syntax_node5(v___y_1583_, v___x_1603_, v___x_1605_, v___x_1607_, v___x_1609_, v___x_1440_, v___x_1611_);
v___x_1613_ = l_Lean_Syntax_node1(v___y_1583_, v___y_1587_, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1615_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1614_, v___x_1442_);
v___x_1616_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1617_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1618_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1580_, 5);
lean_inc_n(v___y_1584_, 5);
v___x_1619_ = l_Lean_addMacroScope(v___y_1584_, v___x_1618_, v___y_1580_);
lean_inc_n(v___y_1589_, 5);
v___x_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1446_);
lean_ctor_set(v___x_1620_, 1, v___y_1589_);
lean_inc_n(v___y_1593_, 6);
v___x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___y_1593_);
v___x_1622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1583_);
lean_ctor_set(v___x_1622_, 1, v___x_1617_);
lean_ctor_set(v___x_1622_, 2, v___x_1619_);
lean_ctor_set(v___x_1622_, 3, v___x_1621_);
v___x_1623_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1616_, v___x_1622_, v___x_1597_);
v___x_1624_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1625_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1626_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1627_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1628_ = l_Lean_addMacroScope(v___y_1584_, v___x_1627_, v___y_1580_);
v___x_1629_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___y_1589_);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___y_1593_);
v___x_1632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1632_, 0, v___y_1583_);
lean_ctor_set(v___x_1632_, 1, v___x_1626_);
lean_ctor_set(v___x_1632_, 2, v___x_1628_);
lean_ctor_set(v___x_1632_, 3, v___x_1631_);
v___x_1633_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1616_, v___x_1632_, v___x_1597_);
v___x_1634_ = l_Lean_Syntax_node1(v___y_1583_, v___y_1587_, v___x_1633_);
v___x_1635_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1625_, v___x_1605_, v___x_1634_, v___x_1611_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1583_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_inc_ref_n(v___x_1637_, 3);
v___x_1638_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1624_, v___x_1635_, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1640_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1583_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___y_1583_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1447_, v___x_1643_);
v___x_1645_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1639_, v___x_1641_, v___x_1644_);
v___x_1646_ = l_Lean_Syntax_node1(v___y_1583_, v___y_1587_, v___x_1645_);
v___x_1647_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1625_, v___x_1605_, v___x_1646_, v___x_1611_);
v___x_1648_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1624_, v___x_1647_, v___x_1637_);
v___x_1649_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___y_1583_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1447_, v___x_1650_);
v___x_1652_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1614_, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1654_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1655_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
v___x_1656_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27));
v___x_1657_ = l_Lean_addMacroScope(v___y_1584_, v___x_1656_, v___y_1580_);
v___x_1658_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28));
v___x_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___y_1589_);
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v___y_1593_);
v___x_1661_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1583_);
lean_ctor_set(v___x_1661_, 1, v___x_1655_);
lean_ctor_set(v___x_1661_, 2, v___x_1657_);
lean_ctor_set(v___x_1661_, 3, v___x_1660_);
v___x_1662_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1616_, v___x_1661_, v___x_1597_);
v___x_1663_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1583_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1666_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1667_ = l_Lean_addMacroScope(v___y_1584_, v___x_1666_, v___y_1580_);
v___x_1668_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___y_1589_);
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___y_1593_);
v___x_1671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1583_);
lean_ctor_set(v___x_1671_, 1, v___x_1665_);
lean_ctor_set(v___x_1671_, 2, v___x_1667_);
lean_ctor_set(v___x_1671_, 3, v___x_1670_);
v___x_1672_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1616_, v___x_1671_, v___x_1597_);
v___x_1673_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1654_, v___x_1662_, v___x_1664_, v___x_1672_);
v___x_1674_ = l_Lean_Syntax_node1(v___y_1583_, v___y_1587_, v___x_1673_);
v___x_1675_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1625_, v___x_1605_, v___x_1674_, v___x_1611_);
v___x_1676_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34));
v___x_1677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1583_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1653_, v___x_1675_, v___x_1677_);
v___x_1679_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35));
v___x_1680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___y_1583_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1447_, v___x_1680_);
v___x_1682_ = l_Lean_Syntax_node1(v___y_1583_, v___x_1614_, v___x_1681_);
v___x_1683_ = l_Lean_Syntax_node3(v___y_1583_, v___y_1587_, v___x_1652_, v___x_1678_, v___x_1682_);
v___x_1684_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1625_, v___x_1605_, v___x_1683_, v___x_1611_);
v___x_1685_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1624_, v___x_1684_, v___x_1637_);
v___x_1686_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40);
v___x_1687_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41));
v___x_1688_ = l_Lean_addMacroScope(v___y_1584_, v___x_1687_, v___y_1580_);
v___x_1689_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
v___x_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___y_1589_);
v___x_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___y_1593_);
v___x_1692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1692_, 0, v___y_1583_);
lean_ctor_set(v___x_1692_, 1, v___x_1686_);
lean_ctor_set(v___x_1692_, 2, v___x_1688_);
lean_ctor_set(v___x_1692_, 3, v___x_1691_);
v___x_1693_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1616_, v___x_1692_, v___x_1597_);
v___x_1694_ = l_Lean_Syntax_node1(v___y_1583_, v___y_1587_, v___x_1693_);
v___x_1695_ = l_Lean_Syntax_node3(v___y_1583_, v___x_1625_, v___x_1605_, v___x_1694_, v___x_1611_);
v___x_1696_ = l_Lean_Syntax_node2(v___y_1583_, v___x_1624_, v___x_1695_, v___x_1637_);
v___x_1697_ = l_Lean_Syntax_node6(v___y_1583_, v___y_1587_, v___x_1615_, v___x_1623_, v___x_1638_, v___x_1648_, v___x_1685_, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19));
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1583_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37);
v___x_1701_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1702_ = l_Lean_addMacroScope(v___y_1584_, v___x_1701_, v___y_1580_);
v___x_1703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1583_);
lean_ctor_set(v___x_1703_, 1, v___x_1700_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
lean_ctor_set(v___x_1703_, 3, v___y_1593_);
v___x_1704_ = lean_unsigned_to_nat(10u);
v___x_1705_ = lean_mk_empty_array_with_capacity(v___x_1704_);
v___x_1706_ = lean_array_push(v___x_1705_, v___x_1596_);
v___x_1707_ = lean_array_push(v___x_1706_, v___x_1597_);
v___x_1708_ = lean_array_push(v___x_1707_, v___x_1600_);
v___x_1709_ = lean_array_push(v___x_1708_, v___x_1601_);
v___x_1710_ = lean_array_push(v___x_1709_, v___x_1597_);
v___x_1711_ = lean_array_push(v___x_1710_, v___x_1613_);
v___x_1712_ = lean_array_push(v___x_1711_, v___x_1597_);
v___x_1713_ = lean_array_push(v___x_1712_, v___x_1697_);
v___x_1714_ = lean_array_push(v___x_1713_, v___x_1699_);
v___x_1715_ = lean_array_push(v___x_1714_, v___x_1703_);
lean_inc(v___y_1581_);
v___x_1716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1716_, 0, v___y_1583_);
lean_ctor_set(v___x_1716_, 1, v___y_1581_);
lean_ctor_set(v___x_1716_, 2, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1585_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___y_1582_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1428_, v___x_1429_, v___x_1440_, v___x_1445_, v___x_1446_, v___x_1444_, v___x_1448_, v___x_1430_, v___x_1718_, v_a_1415_, v___y_1592_);
v___y_1418_ = v___x_1719_;
goto v___jp_1417_;
}
v___jp_1720_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_inc_ref_n(v___y_1731_, 2);
v___x_1736_ = l_Array_append___redArg(v___y_1731_, v___y_1735_);
lean_dec_ref(v___y_1735_);
lean_inc_n(v___y_1722_, 9);
lean_inc_n(v___y_1732_, 56);
v___x_1737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1732_);
lean_ctor_set(v___x_1737_, 1, v___y_1722_);
lean_ctor_set(v___x_1737_, 2, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1732_);
lean_ctor_set(v___x_1738_, 1, v___y_1722_);
lean_ctor_set(v___x_1738_, 2, v___y_1731_);
v___x_1739_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__6));
lean_inc_ref(v___y_1721_);
v___x_1740_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1721_, v___x_1739_);
lean_inc_ref_n(v___x_1738_, 9);
v___x_1741_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1740_, v___x_1738_);
lean_inc_ref(v___y_1727_);
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1732_);
lean_ctor_set(v___x_1742_, 1, v___y_1727_);
v___x_1743_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0));
lean_inc_ref(v___y_1725_);
v___x_1744_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1725_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
v___x_1746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1732_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1));
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1732_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_1750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1732_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___y_1732_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
lean_inc_ref_n(v___x_1752_, 5);
lean_inc(v___x_1440_);
lean_inc_ref_n(v___x_1746_, 5);
v___x_1753_ = l_Lean_Syntax_node5(v___y_1732_, v___x_1744_, v___x_1746_, v___x_1748_, v___x_1750_, v___x_1440_, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node1(v___y_1732_, v___y_1722_, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3));
v___x_1756_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1755_, v___x_1442_);
v___x_1757_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5));
v___x_1758_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
v___x_1759_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7));
lean_inc_n(v___y_1726_, 6);
lean_inc_n(v___y_1733_, 6);
v___x_1760_ = l_Lean_addMacroScope(v___y_1733_, v___x_1759_, v___y_1726_);
lean_inc_n(v___y_1730_, 6);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1446_);
lean_ctor_set(v___x_1761_, 1, v___y_1730_);
lean_inc_n(v___y_1728_, 7);
v___x_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v___y_1728_);
v___x_1763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1763_, 0, v___y_1732_);
lean_ctor_set(v___x_1763_, 1, v___x_1758_);
lean_ctor_set(v___x_1763_, 2, v___x_1760_);
lean_ctor_set(v___x_1763_, 3, v___x_1762_);
v___x_1764_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1763_, v___x_1738_);
v___x_1765_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9));
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10));
v___x_1767_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
v___x_1768_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13));
v___x_1769_ = l_Lean_addMacroScope(v___y_1733_, v___x_1768_, v___y_1726_);
v___x_1770_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14));
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___y_1730_);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___y_1728_);
v___x_1773_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1773_, 0, v___y_1732_);
lean_ctor_set(v___x_1773_, 1, v___x_1767_);
lean_ctor_set(v___x_1773_, 2, v___x_1769_);
lean_ctor_set(v___x_1773_, 3, v___x_1772_);
v___x_1774_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1773_, v___x_1738_);
v___x_1775_ = l_Lean_Syntax_node1(v___y_1732_, v___y_1722_, v___x_1774_);
v___x_1776_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1766_, v___x_1746_, v___x_1775_, v___x_1752_);
v___x_1777_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15));
v___x_1778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1732_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
lean_inc_ref_n(v___x_1778_, 3);
v___x_1779_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1765_, v___x_1776_, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17));
v___x_1781_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18));
v___x_1782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1732_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19));
v___x_1784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1732_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1447_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1780_, v___x_1782_, v___x_1785_);
v___x_1787_ = l_Lean_Syntax_node1(v___y_1732_, v___y_1722_, v___x_1786_);
v___x_1788_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1766_, v___x_1746_, v___x_1787_, v___x_1752_);
v___x_1789_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1765_, v___x_1788_, v___x_1778_);
v___x_1790_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20));
v___x_1791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___y_1732_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1447_, v___x_1791_);
v___x_1793_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1755_, v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22));
v___x_1795_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24));
v___x_1796_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44);
v___x_1797_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45));
v___x_1798_ = l_Lean_addMacroScope(v___y_1733_, v___x_1797_, v___y_1726_);
v___x_1799_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46));
v___x_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___y_1730_);
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1728_);
v___x_1802_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1732_);
lean_ctor_set(v___x_1802_, 1, v___x_1796_);
lean_ctor_set(v___x_1802_, 2, v___x_1798_);
lean_ctor_set(v___x_1802_, 3, v___x_1801_);
v___x_1803_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1802_, v___x_1738_);
v___x_1804_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29));
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1732_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
v___x_1807_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27));
v___x_1808_ = l_Lean_addMacroScope(v___y_1733_, v___x_1807_, v___y_1726_);
v___x_1809_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28));
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___y_1730_);
v___x_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___y_1728_);
v___x_1812_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1812_, 0, v___y_1732_);
lean_ctor_set(v___x_1812_, 1, v___x_1806_);
lean_ctor_set(v___x_1812_, 2, v___x_1808_);
lean_ctor_set(v___x_1812_, 3, v___x_1811_);
v___x_1813_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1812_, v___x_1738_);
v___x_1814_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
v___x_1815_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32));
v___x_1816_ = l_Lean_addMacroScope(v___y_1733_, v___x_1815_, v___y_1726_);
v___x_1817_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33));
v___x_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___y_1730_);
v___x_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___y_1728_);
v___x_1820_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1820_, 0, v___y_1732_);
lean_ctor_set(v___x_1820_, 1, v___x_1814_);
lean_ctor_set(v___x_1820_, 2, v___x_1816_);
lean_ctor_set(v___x_1820_, 3, v___x_1819_);
v___x_1821_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1820_, v___x_1738_);
lean_inc_ref(v___x_1805_);
v___x_1822_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1795_, v___x_1813_, v___x_1805_, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1795_, v___x_1803_, v___x_1805_, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node1(v___y_1732_, v___y_1722_, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1766_, v___x_1746_, v___x_1824_, v___x_1752_);
v___x_1826_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34));
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___y_1732_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1794_, v___x_1825_, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35));
v___x_1830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___y_1732_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1447_, v___x_1830_);
v___x_1832_ = l_Lean_Syntax_node1(v___y_1732_, v___x_1755_, v___x_1831_);
v___x_1833_ = l_Lean_Syntax_node3(v___y_1732_, v___y_1722_, v___x_1793_, v___x_1828_, v___x_1832_);
v___x_1834_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1766_, v___x_1746_, v___x_1833_, v___x_1752_);
v___x_1835_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1765_, v___x_1834_, v___x_1778_);
v___x_1836_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40);
v___x_1837_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41));
v___x_1838_ = l_Lean_addMacroScope(v___y_1733_, v___x_1837_, v___y_1726_);
v___x_1839_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42));
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v___y_1730_);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___y_1728_);
v___x_1842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1842_, 0, v___y_1732_);
lean_ctor_set(v___x_1842_, 1, v___x_1836_);
lean_ctor_set(v___x_1842_, 2, v___x_1838_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
v___x_1843_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1757_, v___x_1842_, v___x_1738_);
v___x_1844_ = l_Lean_Syntax_node1(v___y_1732_, v___y_1722_, v___x_1843_);
v___x_1845_ = l_Lean_Syntax_node3(v___y_1732_, v___x_1766_, v___x_1746_, v___x_1844_, v___x_1752_);
v___x_1846_ = l_Lean_Syntax_node2(v___y_1732_, v___x_1765_, v___x_1845_, v___x_1778_);
v___x_1847_ = l_Lean_Syntax_node6(v___y_1732_, v___y_1722_, v___x_1756_, v___x_1764_, v___x_1779_, v___x_1789_, v___x_1835_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__19));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___y_1732_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37);
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38));
v___x_1852_ = l_Lean_addMacroScope(v___y_1733_, v___x_1851_, v___y_1726_);
v___x_1853_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1853_, 0, v___y_1732_);
lean_ctor_set(v___x_1853_, 1, v___x_1850_);
lean_ctor_set(v___x_1853_, 2, v___x_1852_);
lean_ctor_set(v___x_1853_, 3, v___y_1728_);
v___x_1854_ = lean_unsigned_to_nat(10u);
v___x_1855_ = lean_mk_empty_array_with_capacity(v___x_1854_);
v___x_1856_ = lean_array_push(v___x_1855_, v___x_1737_);
v___x_1857_ = lean_array_push(v___x_1856_, v___x_1738_);
v___x_1858_ = lean_array_push(v___x_1857_, v___x_1741_);
v___x_1859_ = lean_array_push(v___x_1858_, v___x_1742_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1738_);
v___x_1861_ = lean_array_push(v___x_1860_, v___x_1754_);
v___x_1862_ = lean_array_push(v___x_1861_, v___x_1738_);
v___x_1863_ = lean_array_push(v___x_1862_, v___x_1847_);
v___x_1864_ = lean_array_push(v___x_1863_, v___x_1849_);
v___x_1865_ = lean_array_push(v___x_1864_, v___x_1853_);
lean_inc(v___y_1724_);
v___x_1866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1732_);
lean_ctor_set(v___x_1866_, 1, v___y_1724_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___y_1734_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___y_1723_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_1428_, v___x_1429_, v___x_1440_, v___x_1445_, v___x_1446_, v___x_1444_, v___x_1448_, v___x_1430_, v___x_1868_, v_a_1415_, v___y_1729_);
v___y_1418_ = v___x_1869_;
goto v___jp_1417_;
}
v___jp_1870_:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_Lean_Syntax_isNone(v___x_1438_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1873_ = l_Lean_Syntax_getArg(v___x_1438_, v___x_1435_);
lean_dec(v___x_1438_);
v___x_1874_ = l_Lean_Syntax_getKind(v___x_1873_);
v___x_1875_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllKind___closed__1));
v___x_1876_ = lean_name_eq(v___x_1874_, v___x_1875_);
lean_dec(v___x_1874_);
if (v___x_1876_ == 0)
{
lean_object* v_quotContext_1877_; lean_object* v_currMacroScope_1878_; lean_object* v_ref_1879_; lean_object* v___x_1880_; lean_object* v_a_1881_; lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1920_; 
v_quotContext_1877_ = lean_ctor_get(v_a_1415_, 1);
v_currMacroScope_1878_ = lean_ctor_get(v_a_1415_, 2);
v_ref_1879_ = lean_ctor_get(v_a_1415_, 5);
v___x_1880_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1876_, v_ref_1879_, v_a_1415_, v_a_1416_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_a_1882_ = lean_ctor_get(v___x_1880_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1920_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1920_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1887_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1888_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1881_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 2);
lean_ctor_set(v___x_1884_, 1, v___x_1888_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1881_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1918_; 
v___x_1891_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50);
v___x_1892_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51));
lean_inc(v_currMacroScope_1878_);
lean_inc(v_quotContext_1877_);
v___x_1893_ = l_Lean_addMacroScope(v_quotContext_1877_, v___x_1892_, v_currMacroScope_1878_);
v___x_1894_ = lean_box(0);
v___x_1895_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54));
lean_inc(v_a_1881_);
v___x_1896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1881_);
lean_ctor_set(v___x_1896_, 1, v___x_1891_);
lean_ctor_set(v___x_1896_, 2, v___x_1893_);
lean_ctor_set(v___x_1896_, 3, v___x_1895_);
lean_inc_ref(v___x_1890_);
v___x_1897_ = l_Lean_Syntax_node3(v_a_1881_, v___x_1887_, v___x_1890_, v___x_1890_, v___x_1896_);
v___x_1898_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1876_, v_ref_1879_, v_a_1415_, v_a_1882_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_a_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55));
lean_inc(v_a_1899_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 2);
lean_ctor_set(v___x_1902_, 1, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1899_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1907_ = l_Lean_Syntax_node1(v_a_1899_, v___x_1447_, v___x_1906_);
v___x_1908_ = l_Lean_SourceInfo_fromRef(v_ref_1879_, v___x_1876_);
v___x_1909_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0));
v___x_1910_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1911_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1912_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1913_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1871_) == 1)
{
lean_object* v_val_1914_; lean_object* v___x_1915_; 
v_val_1914_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v___y_1871_, 1);
v___x_1915_ = l_Array_mkArray1___redArg(v_val_1914_);
lean_inc(v_quotContext_1877_);
lean_inc(v_currMacroScope_1878_);
v___y_1580_ = v_currMacroScope_1878_;
v___y_1581_ = v___x_1911_;
v___y_1582_ = v___x_1897_;
v___y_1583_ = v___x_1908_;
v___y_1584_ = v_quotContext_1877_;
v___y_1585_ = v___x_1907_;
v___y_1586_ = v___x_1913_;
v___y_1587_ = v___x_1912_;
v___y_1588_ = v___x_1886_;
v___y_1589_ = v___x_1894_;
v___y_1590_ = v___x_1910_;
v___y_1591_ = v___x_1909_;
v___y_1592_ = v_a_1900_;
v___y_1593_ = v___x_1894_;
v___y_1594_ = v___x_1915_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1916_; 
lean_dec(v___y_1871_);
v___x_1916_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1877_);
lean_inc(v_currMacroScope_1878_);
v___y_1580_ = v_currMacroScope_1878_;
v___y_1581_ = v___x_1911_;
v___y_1582_ = v___x_1897_;
v___y_1583_ = v___x_1908_;
v___y_1584_ = v_quotContext_1877_;
v___y_1585_ = v___x_1907_;
v___y_1586_ = v___x_1913_;
v___y_1587_ = v___x_1912_;
v___y_1588_ = v___x_1886_;
v___y_1589_ = v___x_1894_;
v___y_1590_ = v___x_1910_;
v___y_1591_ = v___x_1909_;
v___y_1592_ = v_a_1900_;
v___y_1593_ = v___x_1894_;
v___y_1594_ = v___x_1916_;
goto v___jp_1579_;
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1921_; lean_object* v_currMacroScope_1922_; lean_object* v_ref_1923_; lean_object* v___x_1924_; lean_object* v_a_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1964_; 
v_quotContext_1921_ = lean_ctor_get(v_a_1415_, 1);
v_currMacroScope_1922_ = lean_ctor_get(v_a_1415_, 2);
v_ref_1923_ = lean_ctor_get(v_a_1415_, 5);
v___x_1924_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1872_, v_ref_1923_, v_a_1415_, v_a_1416_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_a_1926_ = lean_ctor_get(v___x_1924_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1928_ = v___x_1924_;
v_isShared_1929_ = v_isSharedCheck_1964_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1964_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1930_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1931_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1932_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1925_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 2);
lean_ctor_set(v___x_1928_, 1, v___x_1932_);
v___x_1934_ = v___x_1928_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v_a_1943_; lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1962_; 
v___x_1935_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59);
v___x_1936_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60));
lean_inc(v_currMacroScope_1922_);
lean_inc(v_quotContext_1921_);
v___x_1937_ = l_Lean_addMacroScope(v_quotContext_1921_, v___x_1936_, v_currMacroScope_1922_);
v___x_1938_ = lean_box(0);
v___x_1939_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63));
lean_inc(v_a_1925_);
v___x_1940_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1925_);
lean_ctor_set(v___x_1940_, 1, v___x_1935_);
lean_ctor_set(v___x_1940_, 2, v___x_1937_);
lean_ctor_set(v___x_1940_, 3, v___x_1939_);
lean_inc_ref(v___x_1934_);
v___x_1941_ = l_Lean_Syntax_node3(v_a_1925_, v___x_1931_, v___x_1934_, v___x_1934_, v___x_1940_);
v___x_1942_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_1872_, v_ref_1923_, v_a_1415_, v_a_1926_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_a_1944_ = lean_ctor_get(v___x_1942_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1946_ = v___x_1942_;
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64));
lean_inc(v_a_1943_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 2);
lean_ctor_set(v___x_1946_, 1, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1943_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1951_ = l_Lean_Syntax_node1(v_a_1943_, v___x_1447_, v___x_1950_);
v___x_1952_ = l_Lean_SourceInfo_fromRef(v_ref_1923_, v___x_1872_);
v___x_1953_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0));
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_1955_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_1956_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_1957_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1871_) == 1)
{
lean_object* v_val_1958_; lean_object* v___x_1959_; 
v_val_1958_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v___y_1871_, 1);
v___x_1959_ = l_Array_mkArray1___redArg(v_val_1958_);
lean_inc(v_quotContext_1921_);
lean_inc(v_currMacroScope_1922_);
v___y_1450_ = v_a_1944_;
v___y_1451_ = v___x_1957_;
v___y_1452_ = v_currMacroScope_1922_;
v___y_1453_ = v___x_1941_;
v___y_1454_ = v___x_1954_;
v___y_1455_ = v___x_1938_;
v___y_1456_ = v___x_1955_;
v___y_1457_ = v___x_1952_;
v___y_1458_ = v___x_1953_;
v___y_1459_ = v___x_1930_;
v___y_1460_ = v___x_1951_;
v___y_1461_ = v___x_1956_;
v___y_1462_ = v___x_1938_;
v___y_1463_ = v_quotContext_1921_;
v___y_1464_ = v___x_1959_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1960_; 
lean_dec(v___y_1871_);
v___x_1960_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1921_);
lean_inc(v_currMacroScope_1922_);
v___y_1450_ = v_a_1944_;
v___y_1451_ = v___x_1957_;
v___y_1452_ = v_currMacroScope_1922_;
v___y_1453_ = v___x_1941_;
v___y_1454_ = v___x_1954_;
v___y_1455_ = v___x_1938_;
v___y_1456_ = v___x_1955_;
v___y_1457_ = v___x_1952_;
v___y_1458_ = v___x_1953_;
v___y_1459_ = v___x_1930_;
v___y_1460_ = v___x_1951_;
v___y_1461_ = v___x_1956_;
v___y_1462_ = v___x_1938_;
v___y_1463_ = v_quotContext_1921_;
v___y_1464_ = v___x_1960_;
goto v___jp_1449_;
}
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1965_; lean_object* v_currMacroScope_1966_; lean_object* v_ref_1967_; lean_object* v___x_1968_; lean_object* v_a_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v___x_1438_);
v_quotContext_1965_ = lean_ctor_get(v_a_1415_, 1);
v_currMacroScope_1966_ = lean_ctor_get(v_a_1415_, 2);
v_ref_1967_ = lean_ctor_get(v_a_1415_, 5);
v___x_1968_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1967_, v_a_1415_, v_a_1416_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_a_1970_ = lean_ctor_get(v___x_1968_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1972_ = v___x_1968_;
v_isShared_1973_ = v_isSharedCheck_2009_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2009_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1974_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17));
v___x_1975_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48));
v___x_1976_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49));
lean_inc(v_a_1969_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 2);
lean_ctor_set(v___x_1972_, 1, v___x_1976_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_1969_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2007_; 
v___x_1979_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66);
v___x_1980_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67));
lean_inc(v_currMacroScope_1966_);
lean_inc(v_quotContext_1965_);
v___x_1981_ = l_Lean_addMacroScope(v_quotContext_1965_, v___x_1980_, v_currMacroScope_1966_);
v___x_1982_ = lean_box(0);
v___x_1983_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70));
lean_inc(v_a_1969_);
v___x_1984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1969_);
lean_ctor_set(v___x_1984_, 1, v___x_1979_);
lean_ctor_set(v___x_1984_, 2, v___x_1981_);
lean_ctor_set(v___x_1984_, 3, v___x_1983_);
lean_inc_ref(v___x_1978_);
v___x_1985_ = l_Lean_Syntax_node3(v_a_1969_, v___x_1975_, v___x_1978_, v___x_1978_, v___x_1984_);
v___x_1986_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_1967_, v_a_1415_, v_a_1970_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_a_1988_ = lean_ctor_get(v___x_1986_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_2007_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2007_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71));
lean_inc(v_a_1987_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 2);
lean_ctor_set(v___x_1990_, 1, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_1987_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1995_ = l_Lean_Syntax_node1(v_a_1987_, v___x_1447_, v___x_1994_);
v___x_1996_ = 0;
v___x_1997_ = l_Lean_SourceInfo_fromRef(v_ref_1967_, v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__0));
v___x_1999_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56));
v___x_2000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57));
v___x_2001_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2002_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
if (lean_obj_tag(v___y_1871_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2004_; 
v_val_2003_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v___y_1871_, 1);
v___x_2004_ = l_Array_mkArray1___redArg(v_val_2003_);
lean_inc(v_quotContext_1965_);
lean_inc(v_currMacroScope_1966_);
v___y_1721_ = v___x_1974_;
v___y_1722_ = v___x_2001_;
v___y_1723_ = v___x_1985_;
v___y_1724_ = v___x_2000_;
v___y_1725_ = v___x_1998_;
v___y_1726_ = v_currMacroScope_1966_;
v___y_1727_ = v___x_1999_;
v___y_1728_ = v___x_1982_;
v___y_1729_ = v_a_1988_;
v___y_1730_ = v___x_1982_;
v___y_1731_ = v___x_2002_;
v___y_1732_ = v___x_1997_;
v___y_1733_ = v_quotContext_1965_;
v___y_1734_ = v___x_1995_;
v___y_1735_ = v___x_2004_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_2005_; 
lean_dec(v___y_1871_);
v___x_2005_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31));
lean_inc(v_quotContext_1965_);
lean_inc(v_currMacroScope_1966_);
v___y_1721_ = v___x_1974_;
v___y_1722_ = v___x_2001_;
v___y_1723_ = v___x_1985_;
v___y_1724_ = v___x_2000_;
v___y_1725_ = v___x_1998_;
v___y_1726_ = v_currMacroScope_1966_;
v___y_1727_ = v___x_1999_;
v___y_1728_ = v___x_1982_;
v___y_1729_ = v_a_1988_;
v___y_1730_ = v___x_1982_;
v___y_1731_ = v___x_2002_;
v___y_1732_ = v___x_1997_;
v___y_1733_ = v_quotContext_1965_;
v___y_1734_ = v___x_1995_;
v___y_1735_ = v___x_2005_;
goto v___jp_1720_;
}
}
}
}
}
}
}
}
v___jp_1417_:
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1419_ = lean_ctor_get(v___y_1418_, 0);
v_a_1420_ = lean_ctor_get(v___y_1418_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___y_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___y_1418_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_inc(v_a_1419_);
lean_dec(v___y_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1419_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___boxed(lean_object* v_x_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(v_x_2020_, v_a_2021_, v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2023_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = l_Lean_Parser_Tactic_optConfig;
v___x_2035_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__3));
v___x_2036_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2037_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v___x_2035_);
lean_ctor_set(v___x_2037_, 2, v___x_2034_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = l_Lean_Parser_Tactic_discharger;
v___x_2039_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2038_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2042_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4);
v___x_2043_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2044_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
lean_ctor_set(v___x_2044_, 2, v___x_2041_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2053_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6);
v___x_2054_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2055_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
lean_ctor_set(v___x_2055_, 2, v___x_2052_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = l_Lean_Parser_Tactic_simpLemma;
v___x_2060_ = l_Lean_Parser_Tactic_simpErase;
v___x_2061_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_2062_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
lean_ctor_set(v___x_2062_, 2, v___x_2059_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_2064_ = l_Lean_Parser_Tactic_simpStar;
v___x_2065_ = ((lean_object*)(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10));
v___x_2066_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2064_);
lean_ctor_set(v___x_2066_, 2, v___x_2063_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18(void){
_start:
{
uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2071_ = 0;
v___x_2072_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_2073_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_2074_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__14, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14);
v___x_2075_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___x_2073_);
lean_ctor_set(v___x_2075_, 2, v___x_2072_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*3, v___x_2071_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__18, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18);
v___x_2077_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_2078_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2079_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
lean_ctor_set(v___x_2079_, 2, v___x_2076_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_2083_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__19, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19);
v___x_2084_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2085_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__21, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21);
v___x_2087_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2090_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10);
v___x_2091_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2092_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
lean_ctor_set(v___x_2092_, 2, v___x_2089_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2093_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2094_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__23, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23);
v___x_2095_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2096_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
lean_ctor_set(v___x_2096_, 2, v___x_2093_);
return v___x_2096_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2097_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__24, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24);
v___x_2098_ = lean_unsigned_to_nat(1022u);
v___x_2099_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1));
v___x_2100_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v___x_2097_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAutoUnfold(void){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__25, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
v___x_2104_ = l_String_toRawSubstring_x27(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(lean_object* v_s_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_quotContext_2110_; lean_object* v_currMacroScope_2111_; lean_object* v_ref_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_quotContext_2110_ = lean_ctor_get(v_a_2108_, 1);
v_currMacroScope_2111_ = lean_ctor_get(v_a_2108_, 2);
v_ref_2112_ = lean_ctor_get(v_a_2108_, 5);
v___x_2113_ = 0;
v___x_2114_ = l_Lean_SourceInfo_fromRef(v_ref_2112_, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2116_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2117_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2118_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2119_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2114_, 8);
v___x_2120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2114_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2122_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2111_, 2);
lean_inc_n(v_quotContext_2110_, 2);
v___x_2123_ = l_Lean_addMacroScope(v_quotContext_2110_, v___x_2122_, v_currMacroScope_2111_);
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2114_);
lean_ctor_set(v___x_2125_, 1, v___x_2121_);
lean_ctor_set(v___x_2125_, 2, v___x_2123_);
lean_ctor_set(v___x_2125_, 3, v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2114_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77);
v___x_2129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78));
v___x_2130_ = l_Lean_addMacroScope(v_quotContext_2110_, v___x_2129_, v_currMacroScope_2111_);
v___x_2131_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82));
v___x_2132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2114_);
lean_ctor_set(v___x_2132_, 1, v___x_2128_);
lean_ctor_set(v___x_2132_, 2, v___x_2130_);
lean_ctor_set(v___x_2132_, 3, v___x_2131_);
v___x_2133_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2114_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_Syntax_node5(v___x_2114_, v___x_2118_, v___x_2120_, v___x_2125_, v___x_2127_, v___x_2132_, v___x_2134_);
v___x_2136_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2117_, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2116_, v___x_2136_);
v___x_2138_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2115_, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65));
v___x_2140_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68));
v___x_2141_ = l_Lean_Syntax_setKind(v_s_2107_, v___x_2140_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = l_Lean_Syntax_getArg(v___x_2141_, v___x_2142_);
v___x_2144_ = 1;
v___x_2145_ = l_Lean_mkAtomFrom(v___x_2143_, v___x_2139_, v___x_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = l_Lean_Syntax_setArg(v___x_2141_, v___x_2142_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = l_Lean_Syntax_getArg(v___x_2146_, v___x_2147_);
v___x_2149_ = l_Lean_Parser_Tactic_appendConfig(v___x_2148_, v___x_2138_);
v___x_2150_ = l_Lean_Syntax_setArg(v___x_2146_, v___x_2147_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_mkSynthetic(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_a_2109_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3____boxed(lean_object* v_s_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(v_s_2153_, v_a_2154_, v_a_2155_);
lean_dec_ref(v_a_2154_);
return v_res_2156_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__4(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = l_Lean_Parser_Tactic_optConfig;
v___x_2168_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__3));
v___x_2169_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2170_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2168_);
lean_ctor_set(v___x_2170_, 2, v___x_2167_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__5(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2172_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__4, &l_Lean_Parser_Tactic_simpArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpArith___closed__4);
v___x_2173_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2174_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2172_);
lean_ctor_set(v___x_2174_, 2, v___x_2171_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__6(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2176_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__5, &l_Lean_Parser_Tactic_simpArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpArith___closed__5);
v___x_2177_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2178_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v___x_2175_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__7(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2180_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__6, &l_Lean_Parser_Tactic_simpArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpArith___closed__6);
v___x_2181_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2182_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2179_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__8(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2184_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__7, &l_Lean_Parser_Tactic_simpArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpArith___closed__7);
v___x_2185_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2186_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2183_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith___closed__9(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__8, &l_Lean_Parser_Tactic_simpArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpArith___closed__8);
v___x_2188_ = lean_unsigned_to_nat(1022u);
v___x_2189_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArith___closed__1));
v___x_2190_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
lean_ctor_set(v___x_2190_, 2, v___x_2187_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArith(void){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArith___closed__9, &l_Lean_Parser_Tactic_simpArith___closed__9_once, _init_l_Lean_Parser_Tactic_simpArith___closed__9);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__4(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = l_Lean_Parser_Tactic_optConfig;
v___x_2203_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__3));
v___x_2204_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2205_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
lean_ctor_set(v___x_2205_, 2, v___x_2202_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__5(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2207_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__4, &l_Lean_Parser_Tactic_simpArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__4);
v___x_2208_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2209_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__6(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2211_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__5, &l_Lean_Parser_Tactic_simpArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__5);
v___x_2212_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2213_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2210_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__7(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__22, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22);
v___x_2215_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__6, &l_Lean_Parser_Tactic_simpArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__6);
v___x_2216_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2217_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
lean_ctor_set(v___x_2217_, 2, v___x_2214_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__8(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2218_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2219_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__7, &l_Lean_Parser_Tactic_simpArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__7);
v___x_2220_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2221_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
lean_ctor_set(v___x_2221_, 2, v___x_2218_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang___closed__9(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2222_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__8, &l_Lean_Parser_Tactic_simpArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__8);
v___x_2223_ = lean_unsigned_to_nat(1022u);
v___x_2224_ = ((lean_object*)(l_Lean_Parser_Tactic_simpArithBang___closed__1));
v___x_2225_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___x_2223_);
lean_ctor_set(v___x_2225_, 2, v___x_2222_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpArithBang(void){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Lean_Parser_Tactic_simpArithBang___closed__9, &l_Lean_Parser_Tactic_simpArithBang___closed__9_once, _init_l_Lean_Parser_Tactic_simpArithBang___closed__9);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = l_Lean_Parser_Tactic_optConfig;
v___x_2238_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3));
v___x_2239_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2240_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set(v___x_2240_, 2, v___x_2237_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2242_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4);
v___x_2243_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2244_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
lean_ctor_set(v___x_2244_, 2, v___x_2241_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2245_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2246_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5);
v___x_2247_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2248_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2246_);
lean_ctor_set(v___x_2248_, 2, v___x_2245_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7(void){
_start:
{
uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2249_ = 0;
v___x_2250_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17));
v___x_2251_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15));
v___x_2252_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__13, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13);
v___x_2253_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
lean_ctor_set(v___x_2253_, 2, v___x_2250_);
lean_ctor_set_uint8(v___x_2253_, sizeof(void*)*3, v___x_2249_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7);
v___x_2255_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12));
v___x_2256_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2257_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
lean_ctor_set(v___x_2257_, 2, v___x_2254_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2258_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20));
v___x_2259_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8);
v___x_2260_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2261_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2259_);
lean_ctor_set(v___x_2261_, 2, v___x_2258_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9);
v___x_2263_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticErw_______00__closed__8));
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2262_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2266_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6);
v___x_2267_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2268_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___x_2266_);
lean_ctor_set(v___x_2268_, 2, v___x_2265_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2269_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11);
v___x_2270_ = lean_unsigned_to_nat(1022u);
v___x_2271_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1));
v___x_2272_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2270_);
lean_ctor_set(v___x_2272_, 2, v___x_2269_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllAutoUnfold(void){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(lean_object* v_s_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_quotContext_2278_; lean_object* v_currMacroScope_2279_; lean_object* v_ref_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_quotContext_2278_ = lean_ctor_get(v_a_2276_, 1);
v_currMacroScope_2279_ = lean_ctor_get(v_a_2276_, 2);
v_ref_2280_ = lean_ctor_get(v_a_2276_, 5);
v___x_2281_ = 0;
v___x_2282_ = l_Lean_SourceInfo_fromRef(v_ref_2280_, v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2284_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2285_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2286_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2287_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2282_, 8);
v___x_2288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2282_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2290_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2279_, 2);
lean_inc_n(v_quotContext_2278_, 2);
v___x_2291_ = l_Lean_addMacroScope(v_quotContext_2278_, v___x_2290_, v_currMacroScope_2279_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2282_);
lean_ctor_set(v___x_2293_, 1, v___x_2289_);
lean_ctor_set(v___x_2293_, 2, v___x_2291_);
lean_ctor_set(v___x_2293_, 3, v___x_2292_);
v___x_2294_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2282_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77);
v___x_2297_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78));
v___x_2298_ = l_Lean_addMacroScope(v_quotContext_2278_, v___x_2297_, v_currMacroScope_2279_);
v___x_2299_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82));
v___x_2300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2282_);
lean_ctor_set(v___x_2300_, 1, v___x_2296_);
lean_ctor_set(v___x_2300_, 2, v___x_2298_);
lean_ctor_set(v___x_2300_, 3, v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2282_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = l_Lean_Syntax_node5(v___x_2282_, v___x_2286_, v___x_2288_, v___x_2293_, v___x_2295_, v___x_2300_, v___x_2302_);
v___x_2304_ = l_Lean_Syntax_node1(v___x_2282_, v___x_2285_, v___x_2303_);
v___x_2305_ = l_Lean_Syntax_node1(v___x_2282_, v___x_2284_, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_node1(v___x_2282_, v___x_2283_, v___x_2305_);
v___x_2307_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61));
v___x_2308_ = l_Lean_Syntax_setKind(v_s_2275_, v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = l_Lean_Syntax_getArg(v___x_2308_, v___x_2309_);
v___x_2311_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_));
v___x_2312_ = 1;
v___x_2313_ = l_Lean_mkAtomFrom(v___x_2310_, v___x_2311_, v___x_2312_);
lean_dec(v___x_2310_);
v___x_2314_ = l_Lean_Syntax_setArg(v___x_2308_, v___x_2309_, v___x_2313_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = l_Lean_Syntax_getArg(v___x_2314_, v___x_2315_);
v___x_2317_ = l_Lean_Parser_Tactic_appendConfig(v___x_2316_, v___x_2306_);
v___x_2318_ = l_Lean_Syntax_setArg(v___x_2314_, v___x_2315_, v___x_2317_);
v___x_2319_ = l_Lean_Syntax_mkSynthetic(v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v_a_2277_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3____boxed(lean_object* v_s_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(v_s_2321_, v_a_2322_, v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2324_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__4(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2335_ = l_Lean_Parser_Tactic_optConfig;
v___x_2336_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__3));
v___x_2337_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2338_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___x_2335_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__5(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2340_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__4, &l_Lean_Parser_Tactic_simpAllArith___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__4);
v___x_2341_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2342_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___x_2340_);
lean_ctor_set(v___x_2342_, 2, v___x_2339_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__6(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2343_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2344_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__5, &l_Lean_Parser_Tactic_simpAllArith___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__5);
v___x_2345_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2346_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2344_);
lean_ctor_set(v___x_2346_, 2, v___x_2343_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__7(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2348_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__6, &l_Lean_Parser_Tactic_simpAllArith___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__6);
v___x_2349_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2350_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2348_);
lean_ctor_set(v___x_2350_, 2, v___x_2347_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith___closed__8(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2351_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__7, &l_Lean_Parser_Tactic_simpAllArith___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__7);
v___x_2352_ = lean_unsigned_to_nat(1022u);
v___x_2353_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArith___closed__1));
v___x_2354_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2352_);
lean_ctor_set(v___x_2354_, 2, v___x_2351_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArith(void){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArith___closed__8, &l_Lean_Parser_Tactic_simpAllArith___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArith___closed__8);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2366_ = l_Lean_Parser_Tactic_optConfig;
v___x_2367_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__3));
v___x_2368_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2369_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v___x_2367_);
lean_ctor_set(v___x_2369_, 2, v___x_2366_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2371_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__4, &l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4);
v___x_2372_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2373_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v___x_2371_);
lean_ctor_set(v___x_2373_, 2, v___x_2370_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2374_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2375_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__5, &l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5);
v___x_2376_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2377_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2375_);
lean_ctor_set(v___x_2377_, 2, v___x_2374_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2378_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2379_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__6, &l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6);
v___x_2380_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2381_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2379_);
lean_ctor_set(v___x_2381_, 2, v___x_2378_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2382_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__7, &l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7);
v___x_2383_ = lean_unsigned_to_nat(1022u);
v___x_2384_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAllArithBang___closed__1));
v___x_2385_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___x_2383_);
lean_ctor_set(v___x_2385_, 2, v___x_2382_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_simpAllArithBang(void){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllArithBang___closed__8, &l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once, _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = l_Lean_Parser_Tactic_optConfig;
v___x_2398_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3));
v___x_2399_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2400_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v___x_2398_);
lean_ctor_set(v___x_2400_, 2, v___x_2397_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2401_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5);
v___x_2402_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4);
v___x_2403_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2404_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
lean_ctor_set(v___x_2404_, 2, v___x_2401_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = ((lean_object*)(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9));
v___x_2406_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5);
v___x_2407_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2408_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2406_);
lean_ctor_set(v___x_2408_, 2, v___x_2405_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2409_ = lean_obj_once(&l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10, &l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once, _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10);
v___x_2410_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6);
v___x_2411_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2412_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v___x_2410_);
lean_ctor_set(v___x_2412_, 2, v___x_2409_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2413_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticErw_______00__closed__9, &l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once, _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9);
v___x_2414_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7);
v___x_2415_ = ((lean_object*)(l_Lean_termEval__prec___00__closed__3));
v___x_2416_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
lean_ctor_set(v___x_2416_, 2, v___x_2413_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8);
v___x_2418_ = lean_unsigned_to_nat(1022u);
v___x_2419_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1));
v___x_2420_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set(v___x_2420_, 2, v___x_2417_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_dsimpAutoUnfold(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9, &l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once, _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(lean_object* v_s_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_quotContext_2425_; lean_object* v_currMacroScope_2426_; lean_object* v_ref_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_quotContext_2425_ = lean_ctor_get(v_a_2423_, 1);
v_currMacroScope_2426_ = lean_ctor_get(v_a_2423_, 2);
v_ref_2427_ = lean_ctor_get(v_a_2423_, 5);
v___x_2428_ = 0;
v___x_2429_ = l_Lean_SourceInfo_fromRef(v_ref_2427_, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1));
v___x_2431_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6));
v___x_2432_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9));
v___x_2433_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11));
v___x_2434_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12));
lean_inc_n(v___x_2429_, 8);
v___x_2435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2429_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_obj_once(&l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_, &l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once, _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
v___x_2437_ = ((lean_object*)(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_));
lean_inc_n(v_currMacroScope_2426_, 2);
lean_inc_n(v_quotContext_2425_, 2);
v___x_2438_ = l_Lean_addMacroScope(v_quotContext_2425_, v___x_2437_, v_currMacroScope_2426_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2429_);
lean_ctor_set(v___x_2440_, 1, v___x_2436_);
lean_ctor_set(v___x_2440_, 2, v___x_2438_);
lean_ctor_set(v___x_2440_, 3, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2429_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77, &l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__77);
v___x_2444_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__78));
v___x_2445_ = l_Lean_addMacroScope(v_quotContext_2425_, v___x_2444_, v_currMacroScope_2426_);
v___x_2446_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___closed__82));
v___x_2447_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2429_);
lean_ctor_set(v___x_2447_, 1, v___x_2443_);
lean_ctor_set(v___x_2447_, 2, v___x_2445_);
lean_ctor_set(v___x_2447_, 3, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30));
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2429_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node5(v___x_2429_, v___x_2433_, v___x_2435_, v___x_2440_, v___x_2442_, v___x_2447_, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2431_, v___x_2451_);
v___x_2453_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2430_, v___x_2452_);
v___x_2454_ = ((lean_object*)(l_Lean_Parser_Tactic_dsimpKind___closed__2));
v___x_2455_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52));
v___x_2456_ = l_Lean_Syntax_setKind(v_s_2422_, v___x_2455_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = l_Lean_Syntax_getArg(v___x_2456_, v___x_2457_);
v___x_2459_ = 1;
v___x_2460_ = l_Lean_mkAtomFrom(v___x_2458_, v___x_2454_, v___x_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = l_Lean_Syntax_setArg(v___x_2456_, v___x_2457_, v___x_2460_);
v___x_2462_ = lean_unsigned_to_nat(1u);
v___x_2463_ = l_Lean_Syntax_getArg(v___x_2461_, v___x_2462_);
v___x_2464_ = l_Lean_Parser_Tactic_appendConfig(v___x_2463_, v___x_2453_);
v___x_2465_ = l_Lean_Syntax_setArg(v___x_2461_, v___x_2462_, v___x_2464_);
v___x_2466_ = l_Lean_Syntax_mkSynthetic(v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v_a_2424_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3____boxed(lean_object* v_s_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(v_s_2468_, v_a_2469_, v_a_2470_);
lean_dec_ref(v_a_2469_);
return v_res_2471_;
}
}
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
