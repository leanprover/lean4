// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Simp
// Imports: public import Lean.Elab.Tactic.Split public import Lean.Elab.Tactic.Conv.Basic public import Lean.Elab.Tactic.SimpTrace
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
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6;
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 165, 42, 136, 187, 206, 234, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalSimp"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(118, 221, 105, 79, 88, 54, 74, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 24, 207, 89, 155, 142, 251, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 89, 177, 67, 170, 210, 173, 232)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object*);
lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpMatch"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 31, 17, 130, 102, 107, 154, 37)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpMatch"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(74, 229, 254, 188, 202, 148, 18, 189)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value;
lean_object* l_Lean_Meta_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 35, 2, 104, 74, 78, 120, 9)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalDSimp"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 180, 75, 129, 95, 56, 151, 69)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 139, 45, 80, 126, 130, 141, 19)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalDSimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 138, 90, 54, 138, 230, 31, 100)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = l_Lean_Elab_Tactic_Conv_changeLhs(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_Simp_Result_getProof(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Elab_Tactic_Conv_updateLhs(x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_15, 0);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
x_19 = x_15;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
x_15 = l_Lean_Meta_simp(x_1, x_2, x_3, x_4, x_14, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_19 = l_Lean_Elab_Tactic_Conv_getLhs___redArg(x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed), 13, 3);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_16);
lean_closure_set(x_21, 2, x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_22 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_18, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_26 = lean_ctor_get(x_22, 0);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
x_27 = x_22;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_34 = lean_ctor_get(x_19, 0);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
x_35 = x_19;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_42 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_43 = x_14;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = 0;
x_12 = 0;
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
x_14 = lean_box(x_11);
x_15 = lean_box(x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_13);
x_17 = l_Lean_Elab_Tactic_withMainContext___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
x_17 = lean_unsigned_to_nat(32u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
x_20 = 5;
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_1);
lean_ctor_set_usize(x_21, 4, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_simp(x_2, x_3, x_4, x_5, x_23, x_10, x_11, x_12, x_13);
lean_dec_ref(x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_201 = lean_unsigned_to_nat(2u);
x_202 = l_Lean_Syntax_getArg(x_2, x_201);
x_248 = lean_unsigned_to_nat(3u);
x_249 = l_Lean_Syntax_getArg(x_2, x_248);
x_250 = l_Lean_Syntax_isNone(x_249);
if (x_250 == 0)
{
uint8_t x_251; 
lean_inc(x_249);
x_251 = l_Lean_Syntax_matchesNull(x_249, x_17);
if (x_251 == 0)
{
lean_object* x_252; 
lean_dec(x_249);
lean_dec(x_202);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_252 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = l_Lean_Syntax_getArg(x_249, x_23);
lean_dec(x_249);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_224 = x_254;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_11;
x_230 = x_12;
x_231 = x_13;
x_232 = x_14;
goto block_247;
}
}
else
{
lean_object* x_255; 
lean_dec(x_249);
x_255 = lean_box(0);
x_224 = x_255;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_11;
x_230 = x_12;
x_231 = x_13;
x_232 = x_14;
goto block_247;
}
block_119:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_35);
x_43 = l_Array_append___redArg(x_35, x_42);
lean_dec_ref(x_42);
lean_inc(x_37);
lean_inc(x_32);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_43);
lean_inc(x_32);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_35);
x_46 = l_Lean_Syntax_node6(x_32, x_25, x_39, x_18, x_26, x_33, x_44, x_45);
x_47 = 0;
x_48 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
lean_inc(x_28);
lean_inc_ref(x_29);
lean_inc(x_31);
lean_inc_ref(x_40);
lean_inc(x_38);
lean_inc_ref(x_41);
lean_inc(x_34);
lean_inc_ref(x_36);
x_49 = l_Lean_Elab_Tactic_mkSimpContext(x_46, x_30, x_47, x_30, x_48, x_36, x_34, x_41, x_38, x_40, x_31, x_29, x_28);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_50, 2);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_28);
lean_inc_ref(x_29);
lean_inc(x_31);
lean_inc_ref(x_40);
x_54 = l_Lean_Elab_Tactic_Conv_getLhs___redArg(x_34, x_40, x_31, x_29, x_28);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed), 14, 4);
lean_closure_set(x_56, 0, x_23);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_51);
lean_closure_set(x_56, 3, x_52);
lean_inc(x_28);
lean_inc_ref(x_29);
lean_inc(x_31);
lean_inc_ref(x_40);
lean_inc(x_38);
lean_inc_ref(x_41);
lean_inc(x_34);
lean_inc_ref(x_36);
x_57 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_53, x_56, x_36, x_34, x_41, x_38, x_40, x_31, x_29, x_28);
lean_dec(x_53);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_28);
lean_inc_ref(x_29);
lean_inc(x_31);
lean_inc_ref(x_40);
x_61 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_59, x_36, x_34, x_41, x_38, x_40, x_31, x_29, x_28);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; uint8_t x_93; 
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_61, 0);
lean_dec(x_94);
x_62 = x_61;
x_63 = x_93;
goto block_92;
}
else
{
lean_dec(x_61);
x_62 = lean_box(0);
x_63 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_90; 
x_64 = lean_ctor_get(x_60, 0);
x_90 = !lean_is_exclusive(x_60);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_60, 1);
lean_dec(x_91);
x_65 = x_60;
x_66 = x_90;
goto block_89;
}
else
{
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_67; 
lean_inc(x_28);
lean_inc_ref(x_29);
x_67 = l_Lean_Elab_Tactic_mkSimpCallStx(x_46, x_64, x_40, x_31, x_29, x_28);
lean_dec_ref(x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (x_66 == 0)
{
lean_ctor_set(x_65, 1, x_68);
lean_ctor_set(x_65, 0, x_69);
x_70 = x_65;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_68);
x_70 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_72, 5, x_71);
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_27);
x_73 = x_62;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_27);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_74 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
x_75 = 4;
x_76 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_24, x_72, x_73, x_74, x_71, x_75, x_29, x_28);
return x_76;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_del_object(x_65);
lean_del_object(x_62);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_81 = lean_ctor_get(x_67, 0);
x_88 = !lean_is_exclusive(x_67);
if (x_88 == 0)
{
x_82 = x_67;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_67);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_46);
lean_dec_ref(x_40);
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
return x_61;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec(x_46);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_95 = lean_ctor_get(x_57, 0);
x_102 = !lean_is_exclusive(x_57);
if (x_102 == 0)
{
x_96 = x_57;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_57);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_103 = lean_ctor_get(x_54, 0);
x_110 = !lean_is_exclusive(x_54);
if (x_110 == 0)
{
x_104 = x_54;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_54);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_46);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_111 = lean_ctor_get(x_49, 0);
x_118 = !lean_is_exclusive(x_49);
if (x_118 == 0)
{
x_112 = x_49;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_49);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
block_149:
{
lean_object* x_138; lean_object* x_139; 
lean_inc_ref(x_130);
x_138 = l_Array_append___redArg(x_130, x_137);
lean_dec_ref(x_137);
lean_inc(x_132);
lean_inc(x_126);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_132);
lean_ctor_set(x_139, 2, x_138);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_129, 0);
lean_inc(x_140);
lean_dec_ref(x_129);
x_141 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc(x_126);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_126);
lean_ctor_set(x_142, 1, x_141);
lean_inc_ref(x_130);
x_143 = l_Array_append___redArg(x_130, x_140);
lean_dec(x_140);
lean_inc(x_132);
lean_inc(x_126);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_126);
lean_ctor_set(x_144, 1, x_132);
lean_ctor_set(x_144, 2, x_143);
x_145 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
lean_inc(x_126);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_126);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Array_mkArray3___redArg(x_142, x_144, x_146);
x_25 = x_120;
x_26 = x_121;
x_27 = x_122;
x_28 = x_123;
x_29 = x_124;
x_30 = x_125;
x_31 = x_127;
x_32 = x_126;
x_33 = x_139;
x_34 = x_128;
x_35 = x_130;
x_36 = x_131;
x_37 = x_132;
x_38 = x_133;
x_39 = x_134;
x_40 = x_135;
x_41 = x_136;
x_42 = x_147;
goto block_119;
}
else
{
lean_object* x_148; 
lean_dec(x_129);
x_148 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
x_25 = x_120;
x_26 = x_121;
x_27 = x_122;
x_28 = x_123;
x_29 = x_124;
x_30 = x_125;
x_31 = x_127;
x_32 = x_126;
x_33 = x_139;
x_34 = x_128;
x_35 = x_130;
x_36 = x_131;
x_37 = x_132;
x_38 = x_133;
x_39 = x_134;
x_40 = x_135;
x_41 = x_136;
x_42 = x_148;
goto block_119;
}
}
block_176:
{
lean_object* x_168; lean_object* x_169; 
lean_inc_ref(x_158);
x_168 = l_Array_append___redArg(x_158, x_167);
lean_dec_ref(x_167);
lean_inc(x_161);
lean_inc(x_155);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_155);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_168);
if (lean_obj_tag(x_163) == 1)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_163, 0);
lean_inc(x_170);
lean_dec_ref(x_163);
x_171 = l_Lean_SourceInfo_fromRef(x_170, x_6);
lean_dec(x_170);
x_172 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Array_mkArray1___redArg(x_173);
x_120 = x_150;
x_121 = x_169;
x_122 = x_151;
x_123 = x_152;
x_124 = x_153;
x_125 = x_154;
x_126 = x_155;
x_127 = x_156;
x_128 = x_157;
x_129 = x_159;
x_130 = x_158;
x_131 = x_160;
x_132 = x_161;
x_133 = x_162;
x_134 = x_164;
x_135 = x_165;
x_136 = x_166;
x_137 = x_174;
goto block_149;
}
else
{
lean_object* x_175; 
lean_dec(x_163);
x_175 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
x_120 = x_150;
x_121 = x_169;
x_122 = x_151;
x_123 = x_152;
x_124 = x_153;
x_125 = x_154;
x_126 = x_155;
x_127 = x_156;
x_128 = x_157;
x_129 = x_159;
x_130 = x_158;
x_131 = x_160;
x_132 = x_161;
x_133 = x_162;
x_134 = x_164;
x_135 = x_165;
x_136 = x_166;
x_137 = x_175;
goto block_149;
}
}
block_200:
{
lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_181, 5);
lean_inc(x_188);
x_189 = 0;
x_190 = l_Lean_SourceInfo_fromRef(x_188, x_189);
x_191 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4));
x_192 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_191);
x_193 = l_Lean_SourceInfo_fromRef(x_24, x_6);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
x_195 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
x_196 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
if (lean_obj_tag(x_187) == 1)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
lean_dec_ref(x_187);
x_198 = l_Array_mkArray1___redArg(x_197);
x_150 = x_192;
x_151 = x_188;
x_152 = x_180;
x_153 = x_181;
x_154 = x_189;
x_155 = x_190;
x_156 = x_185;
x_157 = x_186;
x_158 = x_196;
x_159 = x_178;
x_160 = x_177;
x_161 = x_195;
x_162 = x_179;
x_163 = x_182;
x_164 = x_194;
x_165 = x_183;
x_166 = x_184;
x_167 = x_198;
goto block_176;
}
else
{
lean_object* x_199; 
lean_dec(x_187);
x_199 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
x_150 = x_192;
x_151 = x_188;
x_152 = x_180;
x_153 = x_181;
x_154 = x_189;
x_155 = x_190;
x_156 = x_185;
x_157 = x_186;
x_158 = x_196;
x_159 = x_178;
x_160 = x_177;
x_161 = x_195;
x_162 = x_179;
x_163 = x_182;
x_164 = x_194;
x_165 = x_183;
x_166 = x_184;
x_167 = x_199;
goto block_176;
}
}
block_223:
{
lean_object* x_213; 
x_213 = l_Lean_Syntax_getOptional_x3f(x_202);
lean_dec(x_202);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_box(0);
x_177 = x_205;
x_178 = x_204;
x_179 = x_208;
x_180 = x_212;
x_181 = x_211;
x_182 = x_203;
x_183 = x_209;
x_184 = x_207;
x_185 = x_210;
x_186 = x_206;
x_187 = x_214;
goto block_200;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_222; 
x_215 = lean_ctor_get(x_213, 0);
x_222 = !lean_is_exclusive(x_213);
if (x_222 == 0)
{
x_216 = x_213;
x_217 = x_222;
goto block_221;
}
else
{
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_box(0);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
if (x_217 == 0)
{
x_218 = x_216;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_215);
x_218 = x_220;
goto block_219;
}
block_219:
{
x_177 = x_205;
x_178 = x_204;
x_179 = x_208;
x_180 = x_212;
x_181 = x_211;
x_182 = x_203;
x_183 = x_209;
x_184 = x_207;
x_185 = x_210;
x_186 = x_206;
x_187 = x_218;
goto block_200;
}
}
}
}
block_247:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_unsigned_to_nat(4u);
x_234 = l_Lean_Syntax_getArg(x_2, x_233);
x_235 = l_Lean_Syntax_isNone(x_234);
if (x_235 == 0)
{
uint8_t x_236; 
lean_inc(x_234);
x_236 = l_Lean_Syntax_matchesNull(x_234, x_17);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_202);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_237 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_238 = l_Lean_Syntax_getArg(x_234, x_23);
lean_dec(x_234);
x_239 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_240 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_239);
lean_inc(x_238);
x_241 = l_Lean_Syntax_isOfKind(x_238, x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; 
lean_dec(x_238);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_202);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_242 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = l_Lean_Syntax_getArg(x_238, x_17);
lean_dec(x_238);
x_244 = l_Lean_Syntax_getArgs(x_243);
lean_dec(x_243);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_203 = x_224;
x_204 = x_245;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = x_228;
x_209 = x_229;
x_210 = x_230;
x_211 = x_231;
x_212 = x_232;
goto block_223;
}
}
}
else
{
lean_object* x_246; 
lean_dec(x_234);
x_246 = lean_box(0);
x_203 = x_224;
x_204 = x_246;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = x_228;
x_209 = x_229;
x_210 = x_230;
x_211 = x_231;
x_212 = x_232;
goto block_223;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
x_12 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
x_14 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
x_16 = 1;
x_17 = lean_box(x_15);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed), 15, 6);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_11);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_13);
lean_closure_set(x_19, 5, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_Meta_Split_simpMatch(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_16 = x_12;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_10, 0);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
x_24 = x_10;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0));
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_17 = l_Lean_Elab_Tactic_Conv_getLhs___redArg(x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
x_20 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_21 = l_Lean_Meta_dsimp(x_18, x_16, x_19, x_20, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Tactic_Conv_changeLhs(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_25 = lean_ctor_get(x_21, 0);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
x_26 = x_21;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_33 = lean_ctor_get(x_17, 0);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
x_34 = x_17;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_41 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_42 = x_14;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = 0;
x_12 = 2;
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
x_14 = lean_box(x_11);
x_15 = lean_box(x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed), 13, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_13);
x_17 = l_Lean_Elab_Tactic_withMainContext___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_199 = lean_unsigned_to_nat(2u);
x_200 = l_Lean_Syntax_getArg(x_2, x_199);
x_201 = l_Lean_Syntax_isNone(x_200);
if (x_201 == 0)
{
uint8_t x_202; 
lean_inc(x_200);
x_202 = l_Lean_Syntax_matchesNull(x_200, x_17);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_200);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_203 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_Syntax_getArg(x_200, x_23);
lean_dec(x_200);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_175 = x_205;
x_176 = x_7;
x_177 = x_8;
x_178 = x_9;
x_179 = x_10;
x_180 = x_11;
x_181 = x_12;
x_182 = x_13;
x_183 = x_14;
goto block_198;
}
}
else
{
lean_object* x_206; 
lean_dec(x_200);
x_206 = lean_box(0);
x_175 = x_206;
x_176 = x_7;
x_177 = x_8;
x_178 = x_9;
x_179 = x_10;
x_180 = x_11;
x_181 = x_12;
x_182 = x_13;
x_183 = x_14;
goto block_198;
}
block_117:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = l_Array_append___redArg(x_34, x_42);
lean_dec_ref(x_42);
lean_inc(x_36);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
lean_inc(x_31);
x_45 = l_Lean_Syntax_node6(x_36, x_27, x_40, x_18, x_31, x_38, x_44, x_31);
x_46 = 2;
x_47 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
lean_inc(x_30);
lean_inc_ref(x_35);
lean_inc(x_41);
lean_inc_ref(x_26);
lean_inc(x_37);
lean_inc_ref(x_28);
lean_inc(x_29);
lean_inc_ref(x_25);
x_48 = l_Lean_Elab_Tactic_mkSimpContext(x_45, x_33, x_46, x_33, x_47, x_25, x_29, x_28, x_37, x_26, x_41, x_35, x_30);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
lean_dec(x_49);
lean_inc(x_30);
lean_inc_ref(x_35);
lean_inc(x_41);
lean_inc_ref(x_26);
x_51 = l_Lean_Elab_Tactic_Conv_getLhs___redArg(x_29, x_26, x_41, x_35, x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
x_54 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
lean_inc(x_30);
lean_inc_ref(x_35);
lean_inc(x_41);
lean_inc_ref(x_26);
x_55 = l_Lean_Meta_dsimp(x_52, x_50, x_53, x_54, x_26, x_41, x_35, x_30);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_30);
lean_inc_ref(x_35);
lean_inc(x_41);
lean_inc_ref(x_26);
x_59 = l_Lean_Elab_Tactic_Conv_changeLhs(x_57, x_25, x_29, x_28, x_37, x_26, x_41, x_35, x_30);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; uint8_t x_91; 
x_91 = !lean_is_exclusive(x_59);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_59, 0);
lean_dec(x_92);
x_60 = x_59;
x_61 = x_91;
goto block_90;
}
else
{
lean_dec(x_59);
x_60 = lean_box(0);
x_61 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_88; 
x_62 = lean_ctor_get(x_58, 0);
x_88 = !lean_is_exclusive(x_58);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_58, 1);
lean_dec(x_89);
x_63 = x_58;
x_64 = x_88;
goto block_87;
}
else
{
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_65; 
lean_inc(x_30);
lean_inc_ref(x_35);
x_65 = l_Lean_Elab_Tactic_mkSimpCallStx(x_45, x_62, x_26, x_41, x_35, x_30);
lean_dec_ref(x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_66);
lean_ctor_set(x_63, 0, x_67);
x_68 = x_63;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_66);
x_68 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_69);
if (x_61 == 0)
{
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_32);
x_71 = x_60;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_32);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_72 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
x_73 = 4;
x_74 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_24, x_70, x_71, x_72, x_69, x_73, x_35, x_30);
return x_74;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_del_object(x_63);
lean_del_object(x_60);
lean_dec_ref(x_35);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_24);
x_79 = lean_ctor_get(x_65, 0);
x_86 = !lean_is_exclusive(x_65);
if (x_86 == 0)
{
x_80 = x_65;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_65);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
else
{
lean_dec(x_58);
lean_dec(x_45);
lean_dec(x_41);
lean_dec_ref(x_35);
lean_dec(x_32);
lean_dec(x_30);
lean_dec_ref(x_26);
lean_dec(x_24);
return x_59;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
x_93 = lean_ctor_get(x_55, 0);
x_100 = !lean_is_exclusive(x_55);
if (x_100 == 0)
{
x_94 = x_55;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_55);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec_ref(x_50);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
x_101 = lean_ctor_get(x_51, 0);
x_108 = !lean_is_exclusive(x_51);
if (x_108 == 0)
{
x_102 = x_51;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_51);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
x_109 = lean_ctor_get(x_48, 0);
x_116 = !lean_is_exclusive(x_48);
if (x_116 == 0)
{
x_110 = x_48;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_48);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
block_147:
{
lean_object* x_136; lean_object* x_137; 
lean_inc_ref(x_127);
x_136 = l_Array_append___redArg(x_127, x_135);
lean_dec_ref(x_135);
lean_inc(x_133);
lean_inc(x_129);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_129);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_136);
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
lean_dec_ref(x_128);
x_139 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc(x_129);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set(x_140, 1, x_139);
lean_inc_ref(x_127);
x_141 = l_Array_append___redArg(x_127, x_138);
lean_dec(x_138);
lean_inc(x_133);
lean_inc(x_129);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_129);
lean_ctor_set(x_142, 1, x_133);
lean_ctor_set(x_142, 2, x_141);
x_143 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
lean_inc(x_129);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_129);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Array_mkArray3___redArg(x_140, x_142, x_144);
x_25 = x_118;
x_26 = x_119;
x_27 = x_120;
x_28 = x_121;
x_29 = x_122;
x_30 = x_123;
x_31 = x_124;
x_32 = x_125;
x_33 = x_126;
x_34 = x_127;
x_35 = x_130;
x_36 = x_129;
x_37 = x_131;
x_38 = x_137;
x_39 = x_133;
x_40 = x_132;
x_41 = x_134;
x_42 = x_145;
goto block_117;
}
else
{
lean_object* x_146; 
lean_dec(x_128);
x_146 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
x_25 = x_118;
x_26 = x_119;
x_27 = x_120;
x_28 = x_121;
x_29 = x_122;
x_30 = x_123;
x_31 = x_124;
x_32 = x_125;
x_33 = x_126;
x_34 = x_127;
x_35 = x_130;
x_36 = x_129;
x_37 = x_131;
x_38 = x_137;
x_39 = x_133;
x_40 = x_132;
x_41 = x_134;
x_42 = x_146;
goto block_117;
}
}
block_174:
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_156, 5);
lean_inc(x_158);
x_159 = 0;
x_160 = l_Lean_SourceInfo_fromRef(x_158, x_159);
x_161 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0));
x_162 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_161);
x_163 = l_Lean_SourceInfo_fromRef(x_24, x_6);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
x_165 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
x_166 = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
lean_inc(x_160);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_166);
if (lean_obj_tag(x_148) == 1)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_148, 0);
lean_inc(x_168);
lean_dec_ref(x_148);
x_169 = l_Lean_SourceInfo_fromRef(x_168, x_6);
lean_dec(x_168);
x_170 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Array_mkArray1___redArg(x_171);
x_118 = x_150;
x_119 = x_154;
x_120 = x_162;
x_121 = x_152;
x_122 = x_151;
x_123 = x_157;
x_124 = x_167;
x_125 = x_158;
x_126 = x_159;
x_127 = x_166;
x_128 = x_149;
x_129 = x_160;
x_130 = x_156;
x_131 = x_153;
x_132 = x_164;
x_133 = x_165;
x_134 = x_155;
x_135 = x_172;
goto block_147;
}
else
{
lean_object* x_173; 
lean_dec(x_148);
x_173 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
x_118 = x_150;
x_119 = x_154;
x_120 = x_162;
x_121 = x_152;
x_122 = x_151;
x_123 = x_157;
x_124 = x_167;
x_125 = x_158;
x_126 = x_159;
x_127 = x_166;
x_128 = x_149;
x_129 = x_160;
x_130 = x_156;
x_131 = x_153;
x_132 = x_164;
x_133 = x_165;
x_134 = x_155;
x_135 = x_173;
goto block_147;
}
}
block_198:
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_unsigned_to_nat(3u);
x_185 = l_Lean_Syntax_getArg(x_2, x_184);
x_186 = l_Lean_Syntax_isNone(x_185);
if (x_186 == 0)
{
uint8_t x_187; 
lean_inc(x_185);
x_187 = l_Lean_Syntax_matchesNull(x_185, x_17);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_188 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = l_Lean_Syntax_getArg(x_185, x_23);
lean_dec(x_185);
x_190 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_191 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_190);
lean_inc(x_189);
x_192 = l_Lean_Syntax_isOfKind(x_189, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_193 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = l_Lean_Syntax_getArg(x_189, x_17);
lean_dec(x_189);
x_195 = l_Lean_Syntax_getArgs(x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_148 = x_175;
x_149 = x_196;
x_150 = x_176;
x_151 = x_177;
x_152 = x_178;
x_153 = x_179;
x_154 = x_180;
x_155 = x_181;
x_156 = x_182;
x_157 = x_183;
goto block_174;
}
}
}
else
{
lean_object* x_197; 
lean_dec(x_185);
x_197 = lean_box(0);
x_148 = x_175;
x_149 = x_197;
x_150 = x_176;
x_151 = x_177;
x_152 = x_178;
x_153 = x_179;
x_154 = x_180;
x_155 = x_181;
x_156 = x_182;
x_157 = x_183;
goto block_174;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
x_12 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
x_14 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
x_16 = 1;
x_17 = lean_box(x_15);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_11);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_13);
lean_closure_set(x_19, 5, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Split(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Split(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
