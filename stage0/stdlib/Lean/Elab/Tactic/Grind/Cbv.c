// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Cbv
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.Cbv.Main
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "symCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(36, 127, 132, 126, 172, 148, 105, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(13, 243, 229, 135, 51, 1, 103, 236)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(120, 210, 159, 84, 81, 29, 199, 54)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 46, 90, 65, 171, 6, 40, 84)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(79, 189, 82, 19, 33, 186, 209, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__17_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 249, 251, 166, 171, 222, 99, 92)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 45, 178, 140, 188, 63, 67, 107)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalSymCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(169, 127, 109, 100, 162, 59, 237, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(lean_object* v_mvarId_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_1_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed(lean_object* v_mvarId_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(v_mvarId_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1(lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_25_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; 
lean_dec_ref_known(v___x_34_, 1);
v___x_35_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v_toGoalState_37_; lean_object* v_mvarId_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_62_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_a_36_);
lean_dec_ref_known(v___x_35_, 1);
v_toGoalState_37_ = lean_ctor_get(v_a_36_, 0);
v_mvarId_38_ = lean_ctor_get(v_a_36_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_a_36_);
if (v_isSharedCheck_62_ == 0)
{
v___x_40_ = v_a_36_;
v_isShared_41_ = v_isSharedCheck_62_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_mvarId_38_);
lean_inc(v_toGoalState_37_);
lean_dec(v_a_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_62_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___f_42_; lean_object* v___x_43_; 
v___f_42_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_42_, 0, v_mvarId_38_);
v___x_43_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_42_, v___y_25_, v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v___x_43_, 1);
if (lean_obj_tag(v_a_44_) == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_del_object(v___x_40_);
lean_dec_ref(v_toGoalState_37_);
v___x_45_ = lean_box(0);
v___x_46_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_45_, v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
return v___x_46_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_49_; 
v_val_47_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v_a_44_, 1);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_val_47_);
v___x_49_ = v___x_40_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_toGoalState_37_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_val_47_);
v___x_49_ = v_reuseFailAlloc_53_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_51_, v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
return v___x_52_;
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_del_object(v___x_40_);
lean_dec_ref(v_toGoalState_37_);
v_a_54_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_43_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_43_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_63_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_35_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_35_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___boxed(lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1(v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; 
v___f_91_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___closed__0));
v___x_92_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_91_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___boxed(lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv(lean_object* v_x_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___boxed(lean_object* v_x_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv(v_x_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_x_114_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1(){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_177_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5));
v___x_179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__21));
v___x_180_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___boxed), 10, 0);
v___x_181_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_177_, v___x_178_, v___x_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1();
return v_res_183_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Cbv(builtin);
}
#ifdef __cplusplus
}
#endif
