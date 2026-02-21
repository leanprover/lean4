// Lean compiler output
// Module: Lean.Elab.Tactic.Injection
// Imports: public import Lean.Meta.Tactic.Injection public import Lean.Meta.Tactic.Assumption public import Lean.Elab.Tactic.ElabTerm
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "too many identifiers provided, unused: "};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injection"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 140, 244, 245, 189, 133, 170, 178)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 123, 69, 153, 82, 151, 103, 113)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalInjection"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(114, 174, 52, 90, 204, 193, 227, 90)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)(((size_t)(103) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value),((lean_object*)(((size_t)(103) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value),((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "injections"};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 237, 111, 89, 101, 171, 168, 71)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value;
lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 83, 22, 173, 194, 141, 92, 179)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalInjections"};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 143, 238, 162, 211, 112, 230, 217)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_array_to_list(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofName(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = l_List_isEmpty___redArg(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_obj_once(&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1, &l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once, _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(x_3, x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_15, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_assumptionCore(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
lean_inc(x_22);
x_23 = l_Lean_Meta_injection(x_22, x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
x_26 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(x_25, x_22, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = lean_box(0);
x_12 = x_27;
x_13 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_26;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 2);
lean_inc(x_29);
lean_dec_ref(x_24);
x_30 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
x_31 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(x_30, x_22, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_32 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_12 = x_33;
x_13 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_31;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
block_20:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_12, x_4, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalInjection___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Elab_Tactic_elabAsFVar(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(x_17);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___lam__0___boxed), 11, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalInjection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unsigned_to_nat(5u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_1);
lean_inc(x_22);
x_24 = l_Lean_Meta_injections(x_22, x_1, x_23, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
x_27 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(x_26, x_22, x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = lean_box(0);
x_12 = x_28;
x_13 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_27;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec_ref(x_25);
x_31 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
x_32 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(x_31, x_22, x_30, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_33 = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_12 = x_34;
x_13 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_32;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
block_20:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_12, x_4, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalInjections___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_box(1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_to_list(x_14);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___lam__0___boxed), 11, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_11);
x_19 = l_Lean_Elab_Tactic_withMainContext___redArg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalInjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
