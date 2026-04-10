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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(lean_object* v_tacticName_43_, lean_object* v_mvarId_44_, lean_object* v_unusedIds_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(lean_object* v_tacticName_61_, lean_object* v_mvarId_62_, lean_object* v_unusedIds_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v_tacticName_61_, v_mvarId_62_, v_unusedIds_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(lean_object* v_mvarId_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
lean_inc(v_mvarId_70_);
v___x_76_ = l_Lean_MVarId_assumptionCore(v_mvarId_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_91_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_91_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_91_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_91_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = lean_unbox(v_a_77_);
lean_dec(v_a_77_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v_mvarId_70_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_83_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_89_; 
lean_dec(v_mvarId_70_);
v___x_87_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_87_);
v___x_89_ = v___x_79_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
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
lean_dec(v_mvarId_70_);
v_a_92_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_76_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_76_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(lean_object* v_mvarId_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0(lean_object* v_a_110_, lean_object* v___x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_a_122_; lean_object* v___x_133_; 
v___x_133_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_113_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_n(v_a_134_, 2);
lean_dec_ref(v___x_133_);
lean_inc(v___x_111_);
v___x_135_ = l_Lean_Meta_injection(v_a_134_, v_a_110_, v___x_111_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
if (lean_obj_tag(v_a_136_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
v___x_138_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_137_, v_a_134_, v___x_111_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v___x_139_; 
lean_dec_ref(v___x_138_);
v___x_139_ = lean_box(0);
v_a_122_ = v___x_139_;
goto v___jp_121_;
}
else
{
return v___x_138_;
}
}
else
{
lean_object* v_mvarId_140_; lean_object* v_remainingNames_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v___x_111_);
v_mvarId_140_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_mvarId_140_);
v_remainingNames_141_ = lean_ctor_get(v_a_136_, 2);
lean_inc(v_remainingNames_141_);
lean_dec_ref(v_a_136_);
v___x_142_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1));
v___x_143_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_142_, v_a_134_, v_remainingNames_141_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v___x_144_; 
lean_dec_ref(v___x_143_);
v___x_144_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_140_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v___x_144_);
v_a_122_ = v_a_145_;
goto v___jp_121_;
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_144_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_dec(v_mvarId_140_);
return v___x_143_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_a_134_);
lean_dec(v___x_111_);
v_a_154_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_135_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_135_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v___x_111_);
lean_dec(v_a_110_);
v_a_162_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_133_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_133_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_122_, v___y_113_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_132_);
v___x_125_ = v___x_123_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_123_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(lean_object* v_a_170_, lean_object* v___x_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Elab_Tactic_evalInjection___lam__0(v_a_170_, v___x_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object* v_stx_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = l_Lean_Syntax_getArg(v_stx_182_, v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = l_Lean_Elab_Tactic_elabAsFVar(v___x_193_, v___x_194_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___f_200_; lean_object* v___x_201_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v___x_195_);
v___x_197_ = lean_unsigned_to_nat(2u);
v___x_198_ = l_Lean_Syntax_getArg(v_stx_182_, v___x_197_);
v___x_199_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v___x_198_);
lean_dec(v___x_198_);
v___f_200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___lam__0___boxed), 11, 2);
lean_closure_set(v___f_200_, 0, v_a_196_);
lean_closure_set(v___f_200_, 1, v___x_199_);
v___x_201_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_200_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_201_;
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_195_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_195_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object* v_stx_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_Tactic_evalInjection(v_stx_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_stx_210_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_237_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3));
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
v___x_240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___boxed), 10, 0);
v___x_241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_237_, v___x_238_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3(){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6));
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6));
v___x_271_ = l_Lean_addBuiltinDeclarationRanges(v___x_269_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0(lean_object* v_ids_277_, lean_object* v___x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_a_289_; lean_object* v___x_300_; 
v___x_300_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_280_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_n(v_a_301_, 2);
lean_dec_ref(v___x_300_);
v___x_302_ = lean_unsigned_to_nat(5u);
lean_inc(v_ids_277_);
v___x_303_ = l_Lean_Meta_injections(v_a_301_, v_ids_277_, v___x_302_, v___x_278_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
if (lean_obj_tag(v_a_304_) == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
v___x_306_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_305_, v_a_301_, v_ids_277_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v___x_306_);
v___x_307_ = lean_box(0);
v_a_289_ = v___x_307_;
goto v___jp_288_;
}
else
{
return v___x_306_;
}
}
else
{
lean_object* v_mvarId_308_; lean_object* v_remainingNames_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_ids_277_);
v_mvarId_308_ = lean_ctor_get(v_a_304_, 0);
lean_inc(v_mvarId_308_);
v_remainingNames_309_ = lean_ctor_get(v_a_304_, 1);
lean_inc(v_remainingNames_309_);
lean_dec_ref(v_a_304_);
v___x_310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1));
v___x_311_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_310_, v_a_301_, v_remainingNames_309_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_311_);
v___x_312_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_308_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_a_289_ = v_a_313_;
goto v___jp_288_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_dec(v_mvarId_308_);
return v___x_311_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_a_301_);
lean_dec(v_ids_277_);
v_a_322_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_303_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_303_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v___x_278_);
lean_dec(v_ids_277_);
v_a_330_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_300_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_300_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
v___jp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_289_, v___y_280_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_290_, 0);
lean_dec(v_unused_299_);
v___x_292_ = v___x_290_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_290_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(lean_object* v_ids_338_, lean_object* v___x_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Tactic_evalInjections___lam__0(v_ids_338_, v___x_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections(lean_object* v_stx_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_ids_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
v___x_360_ = lean_box(1);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = l_Lean_Syntax_getArg(v_stx_350_, v___x_361_);
v___x_363_ = l_Lean_Syntax_getArgs(v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = lean_array_to_list(v___x_363_);
v___x_365_ = lean_box(0);
v_ids_366_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_364_, v___x_365_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___lam__0___boxed), 11, 2);
lean_closure_set(v___f_367_, 0, v_ids_366_);
lean_closure_set(v___f_367_, 1, v___x_360_);
v___x_368_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_367_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInjections___boxed(lean_object* v_stx_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_Tactic_evalInjections(v_stx_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_stx_369_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1(){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0));
v___x_394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
v___x_395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjections___boxed), 10, 0);
v___x_396_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_392_, v___x_393_, v___x_394_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3(){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2));
v___x_426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6));
v___x_427_ = l_Lean_addBuiltinDeclarationRanges(v___x_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
return v_res_429_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
