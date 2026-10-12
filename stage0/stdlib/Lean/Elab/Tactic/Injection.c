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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "too many identifiers provided, unused: "};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injection"};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 140, 244, 245, 189, 133, 170, 178)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 123, 69, 153, 82, 151, 103, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalInjection"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(114, 174, 52, 90, 204, 193, 227, 90)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)(((size_t)(103) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value),((lean_object*)(((size_t)(103) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value),((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "injections"};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 237, 111, 89, 101, 171, 168, 71)}};
static const lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 83, 22, 173, 194, 141, 92, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalInjections"};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 143, 238, 162, 211, 112, 230, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_head_4_);
lean_dec(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_11_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(lean_object* v_stx_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Lean_Syntax_isNone(v_stx_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = l_Lean_Syntax_getArg(v_stx_15_, v___x_17_);
v___x_19_ = l_Lean_Syntax_getArgs(v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_array_to_list(v___x_19_);
v___x_21_ = lean_box(0);
v___x_22_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_20_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(lean_object* v_stx_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v_stx_24_);
lean_dec(v_stx_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
if (lean_obj_tag(v_a_26_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = l_List_reverse___redArg(v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_head_29_ = lean_ctor_get(v_a_26_, 0);
v_tail_30_ = lean_ctor_get(v_a_26_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_a_26_);
if (v_isSharedCheck_39_ == 0)
{
v___x_32_ = v_a_26_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_tail_30_);
lean_inc(v_head_29_);
lean_dec(v_a_26_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = l_Lean_MessageData_ofName(v_head_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v_a_27_);
lean_ctor_set(v___x_32_, 0, v___x_34_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_27_);
v___x_36_ = v_reuseFailAlloc_38_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
v_a_26_ = v_tail_30_;
v_a_27_ = v___x_36_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0));
v___x_42_ = l_Lean_stringToMessageData(v___x_41_);
return v___x_42_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(lean_object* v_tacticName_43_, lean_object* v_mvarId_44_, lean_object* v_unusedIds_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_List_isEmpty___redArg(v_unusedIds_45_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_52_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1, &l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once, _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1);
v___x_53_ = lean_box(0);
v___x_54_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(v_unusedIds_45_, v___x_53_);
v___x_55_ = l_Lean_MessageData_ofList(v___x_54_);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_52_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
v___x_58_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_43_, v_mvarId_44_, v___x_57_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_unusedIds_45_);
lean_dec(v_mvarId_44_);
lean_dec(v_tacticName_43_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_43_ = stack[0].m_obj;
lean_object* v_mvarId_44_ = stack[1].m_obj;
lean_object* v_unusedIds_45_ = stack[2].m_obj;
lean_object* v_a_46_ = stack[3].m_obj;
lean_object* v_a_47_ = stack[4].m_obj;
lean_object* v_a_48_ = stack[5].m_obj;
lean_object* v_a_49_ = stack[6].m_obj;
lean_object* v_res_61_;
v_res_61_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v_tacticName_43_, v_mvarId_44_, v_unusedIds_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(lean_object* v_tacticName_62_, lean_object* v_mvarId_63_, lean_object* v_unusedIds_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v_tacticName_62_, v_mvarId_63_, v_unusedIds_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_70_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(lean_object* v_mvarId_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_mvarId_71_);
v___x_77_ = l_Lean_MVarId_assumptionCore(v_mvarId_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_92_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_92_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_92_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_92_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; 
v___x_82_ = lean_unbox(v_a_78_);
lean_dec(v_a_78_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v_mvarId_71_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec(v_mvarId_71_);
v___x_88_ = lean_box(0);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_88_);
v___x_90_ = v___x_80_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec(v_mvarId_71_);
v_a_93_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_77_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_77_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_71_ = stack[0].m_obj;
lean_object* v_a_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_a_74_ = stack[3].m_obj;
lean_object* v_a_75_ = stack[4].m_obj;
lean_object* v_res_101_;
v_res_101_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(lean_object* v_mvarId_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_108_;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0(lean_object* v_a_112_, lean_object* v___x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_a_124_; lean_object* v___x_135_; 
v___x_135_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_115_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_n(v_a_136_, 2);
lean_dec_ref_known(v___x_135_, 1);
lean_inc(v___x_113_);
v___x_137_ = l_Lean_Meta_injection(v_a_136_, v_a_112_, v___x_113_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
if (lean_obj_tag(v_a_138_) == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
v___x_140_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_139_, v_a_136_, v___x_113_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v___x_141_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_141_ = lean_box(0);
v_a_124_ = v___x_141_;
goto v___jp_123_;
}
else
{
return v___x_140_;
}
}
else
{
lean_object* v_mvarId_142_; lean_object* v_remainingNames_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_113_);
v_mvarId_142_ = lean_ctor_get(v_a_138_, 0);
lean_inc(v_mvarId_142_);
v_remainingNames_143_ = lean_ctor_get(v_a_138_, 2);
lean_inc(v_remainingNames_143_);
lean_dec_ref_known(v_a_138_, 3);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
v___x_145_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_144_, v_a_136_, v_remainingNames_143_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v___x_146_; 
lean_dec_ref_known(v___x_145_, 1);
v___x_146_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_142_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_146_, 1);
v_a_124_ = v_a_147_;
goto v___jp_123_;
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_146_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_dec(v_mvarId_142_);
return v___x_145_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_136_);
lean_dec(v___x_113_);
v_a_156_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_137_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_137_);
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
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
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
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v___x_113_);
lean_dec(v_a_112_);
v_a_164_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_135_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_135_);
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
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_box(0);
v___x_126_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_124_, v___y_115_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; 
v_unused_134_ = lean_ctor_get(v___x_126_, 0);
lean_dec(v_unused_134_);
v___x_128_ = v___x_126_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_dec(v___x_126_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_125_);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_125_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalInjection___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_112_ = stack[0].m_obj;
lean_object* v___x_113_ = stack[1].m_obj;
lean_object* v___y_114_ = stack[2].m_obj;
lean_object* v___y_115_ = stack[3].m_obj;
lean_object* v___y_116_ = stack[4].m_obj;
lean_object* v___y_117_ = stack[5].m_obj;
lean_object* v___y_118_ = stack[6].m_obj;
lean_object* v___y_119_ = stack[7].m_obj;
lean_object* v___y_120_ = stack[8].m_obj;
lean_object* v___y_121_ = stack[9].m_obj;
lean_object* v_res_172_;
v_res_172_ = l_Lean_Elab_Tactic_evalInjection___lam__0(v_a_112_, v___x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(lean_object* v_a_173_, lean_object* v___x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Tactic_evalInjection___lam__0(v_a_173_, v___x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_184_;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object* v_stx_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = l_Lean_Syntax_getArg(v_stx_185_, v___x_195_);
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_Elab_Tactic_elabAsFVar(v___x_196_, v___x_197_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = lean_unsigned_to_nat(2u);
v___x_201_ = l_Lean_Syntax_getArg(v_stx_185_, v___x_200_);
v___x_202_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v___x_201_);
lean_dec(v___x_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___lam__0___boxed), 11, 2);
lean_closure_set(v___f_203_, 0, v_a_199_);
lean_closure_set(v___f_203_, 1, v___x_202_);
v___x_204_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_203_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
return v___x_204_;
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_198_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_198_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalInjection_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_185_ = stack[0].m_obj;
lean_object* v_a_186_ = stack[1].m_obj;
lean_object* v_a_187_ = stack[2].m_obj;
lean_object* v_a_188_ = stack[3].m_obj;
lean_object* v_a_189_ = stack[4].m_obj;
lean_object* v_a_190_ = stack[5].m_obj;
lean_object* v_a_191_ = stack[6].m_obj;
lean_object* v_a_192_ = stack[7].m_obj;
lean_object* v_a_193_ = stack[8].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_Elab_Tactic_evalInjection(v_stx_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object* v_stx_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Tactic_evalInjection(v_stx_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_stx_214_);
return v_res_224_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_241_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3));
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
v___x_244_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___boxed), 10, 0);
v___x_245_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_241_, v___x_242_, v___x_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_246_;
v_res_246_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
return v_res_248_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3(){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6));
v___x_276_ = l_Lean_addBuiltinDeclarationRanges(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_277_;
v_res_277_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
return v_res_279_;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0(lean_object* v_ids_283_, lean_object* v___x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_a_295_; lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_286_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_n(v_a_307_, 2);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = lean_unsigned_to_nat(5u);
lean_inc(v_ids_283_);
v___x_309_ = l_Lean_Meta_injections(v_a_307_, v_ids_283_, v___x_308_, v___x_284_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
if (lean_obj_tag(v_a_310_) == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
v___x_312_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_311_, v_a_307_, v_ids_283_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
lean_dec_ref_known(v___x_312_, 1);
v___x_313_ = lean_box(0);
v_a_295_ = v___x_313_;
goto v___jp_294_;
}
else
{
return v___x_312_;
}
}
else
{
lean_object* v_mvarId_314_; lean_object* v_remainingNames_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_ids_283_);
v_mvarId_314_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_mvarId_314_);
v_remainingNames_315_ = lean_ctor_get(v_a_310_, 1);
lean_inc(v_remainingNames_315_);
lean_dec_ref_known(v_a_310_, 3);
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
v___x_317_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_316_, v_a_307_, v_remainingNames_315_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; 
lean_dec_ref_known(v___x_317_, 1);
v___x_318_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_314_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v_a_295_ = v_a_319_;
goto v___jp_294_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_318_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_dec(v_mvarId_314_);
return v___x_317_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_a_307_);
lean_dec(v_ids_283_);
v_a_328_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_309_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_309_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v___x_284_);
lean_dec(v_ids_283_);
v_a_336_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_306_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_306_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
v___jp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_box(0);
v___x_297_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_295_, v___y_286_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_297_, 0);
lean_dec(v_unused_305_);
v___x_299_ = v___x_297_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_dec(v___x_297_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_296_);
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_296_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalInjections___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ids_283_ = stack[0].m_obj;
lean_object* v___x_284_ = stack[1].m_obj;
lean_object* v___y_285_ = stack[2].m_obj;
lean_object* v___y_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v___y_289_ = stack[6].m_obj;
lean_object* v___y_290_ = stack[7].m_obj;
lean_object* v___y_291_ = stack[8].m_obj;
lean_object* v___y_292_ = stack[9].m_obj;
lean_object* v_res_344_;
v_res_344_ = l_Lean_Elab_Tactic_evalInjections___lam__0(v_ids_283_, v___x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(lean_object* v_ids_345_, lean_object* v___x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Tactic_evalInjections___lam__0(v_ids_345_, v___x_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_356_;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjections(lean_object* v_stx_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_ids_373_; lean_object* v___f_374_; lean_object* v___x_375_; 
v___x_367_ = lean_box(1);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_368_);
v___x_370_ = l_Lean_Syntax_getArgs(v___x_369_);
lean_dec(v___x_369_);
v___x_371_ = lean_array_to_list(v___x_370_);
v___x_372_ = lean_box(0);
v_ids_373_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_371_, v___x_372_);
v___f_374_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___lam__0___boxed), 11, 2);
lean_closure_set(v___f_374_, 0, v_ids_373_);
lean_closure_set(v___f_374_, 1, v___x_367_);
v___x_375_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_374_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalInjections_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_357_ = stack[0].m_obj;
lean_object* v_a_358_ = stack[1].m_obj;
lean_object* v_a_359_ = stack[2].m_obj;
lean_object* v_a_360_ = stack[3].m_obj;
lean_object* v_a_361_ = stack[4].m_obj;
lean_object* v_a_362_ = stack[5].m_obj;
lean_object* v_a_363_ = stack[6].m_obj;
lean_object* v_a_364_ = stack[7].m_obj;
lean_object* v_a_365_ = stack[8].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_Elab_Tactic_evalInjections(v_stx_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___boxed(lean_object* v_stx_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_evalInjections(v_stx_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_stx_377_);
return v_res_387_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1(){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0));
v___x_402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
v___x_403_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___boxed), 10, 0);
v___x_404_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_400_, v___x_401_, v___x_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_405_;
v_res_405_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
return v_res_407_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3(){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6));
v___x_436_ = l_Lean_addBuiltinDeclarationRanges(v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_437_;
v_res_437_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
return v_res_439_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Injection(builtin);
}
#ifdef __cplusplus
}
#endif
