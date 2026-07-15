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
lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(lean_object* v_mvarId_1_, uint8_t v___x_2_, lean_object* v___x_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_1_, v___x_2_, v___x_3_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed(lean_object* v_mvarId_15_, lean_object* v___x_16_, lean_object* v___x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
uint8_t v___x_513__boxed_28_; lean_object* v_res_29_; 
v___x_513__boxed_28_ = lean_unbox(v___x_16_);
v_res_29_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0(v_mvarId_15_, v___x_513__boxed_28_, v___x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1(lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_32_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v___x_42_; 
lean_dec_ref_known(v___x_41_, 1);
v___x_42_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_33_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v_toGoalState_44_; lean_object* v_mvarId_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_72_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v_toGoalState_44_ = lean_ctor_get(v_a_43_, 0);
v_mvarId_45_ = lean_ctor_get(v_a_43_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_a_43_);
if (v_isSharedCheck_72_ == 0)
{
v___x_47_ = v_a_43_;
v_isShared_48_ = v_isSharedCheck_72_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_mvarId_45_);
lean_inc(v_toGoalState_44_);
lean_dec(v_a_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_72_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v___x_49_ = 1;
v___x_50_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___closed__0));
v___x_51_ = lean_box(v___x_49_);
v___f_52_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_52_, 0, v_mvarId_45_);
lean_closure_set(v___f_52_, 1, v___x_51_);
lean_closure_set(v___f_52_, 2, v___x_50_);
v___x_53_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_52_, v___y_32_, v___y_33_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
if (lean_obj_tag(v_a_54_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_del_object(v___x_47_);
lean_dec_ref(v_toGoalState_44_);
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_55_, v___y_33_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_59_; 
v_val_57_ = lean_ctor_get(v_a_54_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_a_54_, 1);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v_val_57_);
v___x_59_ = v___x_47_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_toGoalState_44_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_val_57_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_61_, v___y_33_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_62_;
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_del_object(v___x_47_);
lean_dec_ref(v_toGoalState_44_);
v_a_64_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_53_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_53_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_42_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_42_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1___boxed(lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___lam__1(v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___closed__0));
v___x_102_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_101_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg___boxed(lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv(lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___redArg(v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___boxed(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv(v_x_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_x_124_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1(){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__5));
v___x_189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___closed__21));
v___x_190_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___boxed), 10, 0);
v___x_191_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_187_, v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1___boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv___regBuiltin___private_Lean_Elab_Tactic_Grind_Cbv_0__Lean_Elab_Tactic_Grind_evalSymCbv__1();
return v_res_193_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
