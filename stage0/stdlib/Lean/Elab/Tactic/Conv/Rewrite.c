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
lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(lean_object* v___y_1_, lean_object* v_term_2_, uint8_t v_symm_3_, lean_object* v_a_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1_ = stack[0].m_obj;
lean_object* v_term_2_ = stack[1].m_obj;
uint8_t v_symm_3_ = stack[2].m_num;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(v___y_1_, v_term_2_, v_symm_3_, v_a_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed(lean_object* v___y_35_, lean_object* v_term_36_, lean_object* v_symm_37_, lean_object* v_a_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_symm_boxed_47_; lean_object* v_res_48_; 
v_symm_boxed_47_ = lean_unbox(v_symm_37_);
v_res_48_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0(v___y_35_, v_term_36_, v_symm_boxed_47_, v_a_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_35_);
return v_res_48_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(lean_object* v_term_49_, uint8_t v_symm_50_, lean_object* v_a_51_, uint8_t v___x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(v_symm_50_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_54_);
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__0___boxed), 12, 5);
lean_closure_set(v___f_63_, 0, v___y_54_);
lean_closure_set(v___f_63_, 1, v_term_49_);
lean_closure_set(v___f_63_, 2, v___x_62_);
lean_closure_set(v___f_63_, 3, v_a_51_);
lean_closure_set(v___f_63_, 4, v___y_53_);
v___x_64_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_63_, v___x_52_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v___x_64_, 1);
v___x_66_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_65_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_eNew_68_; lean_object* v_eqProof_69_; lean_object* v_mvarIds_70_; lean_object* v___x_71_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v_eNew_68_ = lean_ctor_get(v_a_67_, 0);
lean_inc_ref(v_eNew_68_);
v_eqProof_69_ = lean_ctor_get(v_a_67_, 1);
lean_inc_ref(v_eqProof_69_);
v_mvarIds_70_ = lean_ctor_get(v_a_67_, 2);
lean_inc(v_mvarIds_70_);
lean_dec(v_a_67_);
v___x_71_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_eNew_68_, v_eqProof_69_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec_ref(v___y_53_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v___x_72_; 
lean_dec_ref_known(v___x_71_, 1);
v___x_72_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v_a_73_);
lean_ctor_set(v___x_74_, 1, v_mvarIds_70_);
v___x_75_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_74_, v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_54_);
return v___x_75_;
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_mvarIds_70_);
lean_dec(v___y_54_);
v_a_76_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_72_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_72_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
else
{
lean_dec(v_mvarIds_70_);
lean_dec(v___y_54_);
return v___x_71_;
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
v_a_84_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_66_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_66_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
v_a_92_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_64_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_64_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_term_49_ = stack[0].m_obj;
uint8_t v_symm_50_ = stack[1].m_num;
lean_object* v_a_51_ = stack[2].m_obj;
uint8_t v___x_52_ = stack[3].m_num;
lean_object* v___y_53_ = stack[4].m_obj;
lean_object* v___y_54_ = stack[5].m_obj;
lean_object* v___y_55_ = stack[6].m_obj;
lean_object* v___y_56_ = stack[7].m_obj;
lean_object* v___y_57_ = stack[8].m_obj;
lean_object* v___y_58_ = stack[9].m_obj;
lean_object* v___y_59_ = stack[10].m_obj;
lean_object* v___y_60_ = stack[11].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(v_term_49_, v_symm_50_, v_a_51_, v___x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed(lean_object* v_term_101_, lean_object* v_symm_102_, lean_object* v_a_103_, lean_object* v___x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_symm_boxed_114_; uint8_t v___x_1141__boxed_115_; lean_object* v_res_116_; 
v_symm_boxed_114_ = lean_unbox(v_symm_102_);
v___x_1141__boxed_115_ = lean_unbox(v___x_104_);
v_res_116_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1(v_term_101_, v_symm_boxed_114_, v_a_103_, v___x_1141__boxed_115_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_116_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(lean_object* v_a_117_, uint8_t v_symm_118_, lean_object* v_term_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v___x_129_ = 1;
v___x_130_ = lean_box(v_symm_118_);
v___x_131_ = lean_box(v___x_129_);
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__1___boxed), 13, 4);
lean_closure_set(v___f_132_, 0, v_term_119_);
lean_closure_set(v___f_132_, 1, v___x_130_);
lean_closure_set(v___f_132_, 2, v_a_117_);
lean_closure_set(v___f_132_, 3, v___x_131_);
v___x_133_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_132_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_117_ = stack[0].m_obj;
uint8_t v_symm_118_ = stack[1].m_num;
lean_object* v_term_119_ = stack[2].m_obj;
lean_object* v___y_120_ = stack[3].m_obj;
lean_object* v___y_121_ = stack[4].m_obj;
lean_object* v___y_122_ = stack[5].m_obj;
lean_object* v___y_123_ = stack[6].m_obj;
lean_object* v___y_124_ = stack[7].m_obj;
lean_object* v___y_125_ = stack[8].m_obj;
lean_object* v___y_126_ = stack[9].m_obj;
lean_object* v___y_127_ = stack[10].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(v_a_117_, v_symm_118_, v_term_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed(lean_object* v_a_135_, lean_object* v_symm_136_, lean_object* v_term_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v_symm_boxed_147_; lean_object* v_res_148_; 
v_symm_boxed_147_ = lean_unbox(v_symm_136_);
v_res_148_ = l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2(v_a_135_, v_symm_boxed_147_, v_term_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_148_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite(lean_object* v_stx_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = l_Lean_Syntax_getArg(v_stx_154_, v___x_164_);
v___x_166_ = 1;
v___x_167_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRewrite___closed__0));
v___x_168_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_165_, v___x_167_, v___x_166_, v_a_155_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v___f_170_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___lam__2___boxed), 12, 1);
lean_closure_set(v___f_170_, 0, v_a_169_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Lean_Syntax_getArg(v_stx_154_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = l_Lean_Syntax_getArg(v_stx_154_, v___x_173_);
v___x_175_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_172_, v___x_174_, v___f_170_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_168_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_168_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_154_ = stack[0].m_obj;
lean_object* v_a_155_ = stack[1].m_obj;
lean_object* v_a_156_ = stack[2].m_obj;
lean_object* v_a_157_ = stack[3].m_obj;
lean_object* v_a_158_ = stack[4].m_obj;
lean_object* v_a_159_ = stack[5].m_obj;
lean_object* v_a_160_ = stack[6].m_obj;
lean_object* v_a_161_ = stack[7].m_obj;
lean_object* v_a_162_ = stack[8].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Elab_Tactic_Conv_evalRewrite(v_stx_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRewrite___boxed(lean_object* v_stx_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_Tactic_Conv_evalRewrite(v_stx_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_stx_185_);
return v_res_195_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1(){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_216_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__5));
v___x_218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8));
v___x_219_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRewrite___boxed), 10, 0);
v___x_220_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_216_, v___x_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_221_;
v_res_221_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___boxed(lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1();
return v_res_223_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite__1___closed__8));
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___closed__6));
v___x_252_ = l_Lean_addBuiltinDeclarationRanges(v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3___boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Elab_Tactic_Conv_Rewrite_0__Lean_Elab_Tactic_Conv_evalRewrite___regBuiltin_Lean_Elab_Tactic_Conv_evalRewrite_declRange__3();
return v_res_255_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
