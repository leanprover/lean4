// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.LetToHave
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Sym.LetToHave import Lean.Meta.Tactic.Replace import Lean.Meta.Sym.InstantiateMVarsS
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
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`let_to_have` made no progress"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "symLetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(97, 58, 253, 176, 149, 87, 6, 242)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(125, 172, 200, 84, 25, 88, 178, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(8, 216, 189, 84, 204, 46, 201, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 173, 4, 129, 229, 79, 220, 138)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(127, 217, 67, 41, 243, 197, 149, 27)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__17_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 172, 132, 46, 202, 254, 185, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 160, 119, 48, 169, 90, 18, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSymLetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(4, 25, 208, 220, 148, 31, 100, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_53_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v___x_63_; 
lean_dec_ref_known(v___x_62_, 1);
v___x_63_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v_toGoalState_65_; lean_object* v_mvarId_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_129_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
v_toGoalState_65_ = lean_ctor_get(v_a_64_, 0);
v_mvarId_66_ = lean_ctor_get(v_a_64_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_129_ == 0)
{
v___x_68_ = v_a_64_;
v_isShared_69_ = v_isSharedCheck_129_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_mvarId_66_);
lean_inc(v_toGoalState_65_);
lean_dec(v_a_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_129_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; 
lean_inc(v_mvarId_66_);
v___x_70_ = l_Lean_MVarId_getType(v_mvarId_66_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateMVarsS___boxed), 8, 1);
lean_closure_set(v___x_72_, 0, v_a_71_);
v___x_73_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_72_, v___y_53_, v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_n(v_a_74_, 2);
lean_dec_ref_known(v___x_73_, 1);
v___x_75_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___boxed), 8, 1);
lean_closure_set(v___x_75_, 0, v_a_74_);
v___x_76_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_75_, v___y_53_, v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; size_t v___x_100_; size_t v___x_101_; uint8_t v___x_102_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v___x_100_ = lean_ptr_addr(v_a_74_);
lean_dec(v_a_74_);
v___x_101_ = lean_ptr_addr(v_a_77_);
v___x_102_ = lean_usize_dec_eq(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
v___y_79_ = v___y_54_;
v___y_80_ = v___y_57_;
v___y_81_ = v___y_58_;
v___y_82_ = v___y_59_;
v___y_83_ = v___y_60_;
goto v___jp_78_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_a_77_);
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v___x_103_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1);
v___x_104_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v___x_103_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
return v___x_104_;
}
v___jp_78_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_66_, v_a_77_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_a_85_);
v___x_87_ = v___x_68_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_toGoalState_65_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_a_85_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_89_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_90_;
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_del_object(v___x_68_);
lean_dec_ref(v_toGoalState_65_);
v_a_92_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_84_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_84_);
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
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v_a_74_);
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v_a_105_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_76_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_76_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v_a_113_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_73_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_73_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v_a_121_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_70_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_70_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_63_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_63_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___boxed(lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; 
v___f_158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0));
v___x_159_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_158_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed(lean_object* v_x_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(v_x_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_x_181_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(lean_object* v_00_u03b1_192_, lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_193_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___boxed(lean_object* v_00_u03b1_204_, lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(v_00_u03b1_204_, v_msg_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1(){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5));
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21));
v___x_271_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed), 10, 0);
v___x_272_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_268_, v___x_269_, v___x_270_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___boxed(lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
return v_res_274_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_LetToHave(builtin);
}
#ifdef __cplusplus
}
#endif
