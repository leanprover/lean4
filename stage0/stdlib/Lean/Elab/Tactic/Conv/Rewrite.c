// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Rewrite
// Imports: public import Lean.Elab.Tactic.Rewrite public import Lean.Elab.Tactic.Conv.Basic
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 123, 122, 14, 133, 216, 210, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalRewrite"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(30, 157, 142, 87, 101, 101, 170, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(lean_object* v___y_1_, lean_object* v_term_2_, uint8_t v_symm_3_, lean_object* v_a_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_Elab_Tactic_elabRewrite(v_a_14_, v_a_16_, v_term_2_, v_symm_3_, v_a_4_, v___y_5_, v___y_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
return v___x_17_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec(v_a_14_);
lean_dec_ref(v_a_4_);
lean_dec(v_term_2_);
v_a_18_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_15_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref(v_a_4_);
lean_dec(v_term_2_);
v_a_26_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_13_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_13_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed(lean_object* v___y_34_, lean_object* v_term_35_, lean_object* v_symm_36_, lean_object* v_a_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
uint8_t v_symm_boxed_46_; lean_object* v_res_47_; 
v_symm_boxed_46_ = lean_unbox(v_symm_36_);
v_res_47_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(v___y_34_, v_term_35_, v_symm_boxed_46_, v_a_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_34_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(lean_object* v_term_48_, uint8_t v_symm_49_, lean_object* v_a_50_, uint8_t v___x_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(v_symm_49_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_53_);
v___f_62_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed), 12, 5);
lean_closure_set(v___f_62_, 0, v___y_53_);
lean_closure_set(v___f_62_, 1, v_term_48_);
lean_closure_set(v___f_62_, 2, v___x_61_);
lean_closure_set(v___f_62_, 3, v_a_50_);
lean_closure_set(v___f_62_, 4, v___y_52_);
v___x_63_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_62_, v___x_51_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_64_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v_eNew_67_; lean_object* v_eqProof_68_; lean_object* v_mvarIds_69_; lean_object* v___x_70_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
v_eNew_67_ = lean_ctor_get(v_a_66_, 0);
lean_inc_ref(v_eNew_67_);
v_eqProof_68_ = lean_ctor_get(v_a_66_, 1);
lean_inc_ref(v_eqProof_68_);
v_mvarIds_69_ = lean_ctor_get(v_a_66_, 2);
lean_inc(v_mvarIds_69_);
lean_dec(v_a_66_);
v___x_70_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_eNew_67_, v_eqProof_68_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec_ref(v___y_52_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v___x_71_; 
lean_dec_ref_known(v___x_70_, 1);
v___x_71_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_53_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v_a_72_);
lean_ctor_set(v___x_73_, 1, v_mvarIds_69_);
v___x_74_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_73_, v___y_53_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_53_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_mvarIds_69_);
lean_dec(v___y_53_);
v_a_75_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_71_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_71_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_dec(v_mvarIds_69_);
lean_dec(v___y_53_);
return v___x_70_;
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
v_a_83_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_65_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_65_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
v_a_91_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_63_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_63_);
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
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed(lean_object* v_term_99_, lean_object* v_symm_100_, lean_object* v_a_101_, lean_object* v___x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
uint8_t v_symm_boxed_112_; uint8_t v___x_1094__boxed_113_; lean_object* v_res_114_; 
v_symm_boxed_112_ = lean_unbox(v_symm_100_);
v___x_1094__boxed_113_ = lean_unbox(v___x_102_);
v_res_114_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(v_term_99_, v_symm_boxed_112_, v_a_101_, v___x_1094__boxed_113_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(lean_object* v_a_115_, uint8_t v_symm_116_, lean_object* v_term_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___x_131_; 
v___x_127_ = 1;
v___x_128_ = lean_box(v_symm_116_);
v___x_129_ = lean_box(v___x_127_);
v___f_130_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed), 13, 4);
lean_closure_set(v___f_130_, 0, v_term_117_);
lean_closure_set(v___f_130_, 1, v___x_128_);
lean_closure_set(v___f_130_, 2, v_a_115_);
lean_closure_set(v___f_130_, 3, v___x_129_);
v___x_131_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_130_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed(lean_object* v_a_132_, lean_object* v_symm_133_, lean_object* v_term_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
uint8_t v_symm_boxed_144_; lean_object* v_res_145_; 
v_symm_boxed_144_ = lean_unbox(v_symm_133_);
v_res_145_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(v_a_132_, v_symm_boxed_144_, v_term_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite(lean_object* v_stx_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = l_Lean_Syntax_getArg(v_stx_151_, v___x_161_);
v___x_163_ = 1;
v___x_164_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0));
v___x_165_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_162_, v___x_164_, v___x_163_, v_a_152_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
v___f_167_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed), 12, 1);
lean_closure_set(v___f_167_, 0, v_a_166_);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Lean_Syntax_getArg(v_stx_151_, v___x_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = l_Lean_Syntax_getArg(v_stx_151_, v___x_170_);
v___x_172_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_169_, v___x_171_, v___f_167_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_165_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_165_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___boxed(lean_object* v_stx_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_Tactic_Conv_evalRewrite(v_stx_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_stx_181_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1(){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5));
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8));
v___x_215_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___boxed), 10, 0);
v___x_216_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_212_, v___x_213_, v___x_214_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___boxed(lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3(){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8));
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6));
v___x_247_ = l_Lean_addBuiltinDeclarationRanges(v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___boxed(lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
return v_res_249_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
