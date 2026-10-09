// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.LetToHave
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Sym.LetToHave import Lean.Meta.Tactic.Replace
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
lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__0));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_55_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
lean_dec_ref_known(v___x_64_, 1);
v___x_65_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_56_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v_toGoalState_67_; lean_object* v_mvarId_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_120_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
v_toGoalState_67_ = lean_ctor_get(v_a_66_, 0);
v_mvarId_68_ = lean_ctor_get(v_a_66_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_a_66_);
if (v_isSharedCheck_120_ == 0)
{
v___x_70_ = v_a_66_;
v_isShared_71_ = v_isSharedCheck_120_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_mvarId_68_);
lean_inc(v_toGoalState_67_);
lean_dec(v_a_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_120_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; 
lean_inc(v_mvarId_68_);
v___x_72_ = l_Lean_MVarId_getType(v_mvarId_68_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_n(v_a_73_, 2);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___boxed), 8, 1);
lean_closure_set(v___x_74_, 0, v_a_73_);
v___x_75_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_74_, v___y_55_, v___y_56_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_75_, 1);
v___x_99_ = lean_ptr_addr(v_a_73_);
lean_dec(v_a_73_);
v___x_100_ = lean_ptr_addr(v_a_76_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
v___y_78_ = v___y_56_;
v___y_79_ = v___y_59_;
v___y_80_ = v___y_60_;
v___y_81_ = v___y_61_;
v___y_82_ = v___y_62_;
goto v___jp_77_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_a_76_);
lean_del_object(v___x_70_);
lean_dec(v_mvarId_68_);
lean_dec_ref(v_toGoalState_67_);
v___x_102_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1);
v___x_103_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v___x_102_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
return v___x_103_;
}
v___jp_77_:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_68_, v_a_76_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_83_, 1);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v_a_84_);
v___x_86_ = v___x_70_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_toGoalState_67_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_a_84_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_88_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_89_;
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_del_object(v___x_70_);
lean_dec_ref(v_toGoalState_67_);
v_a_91_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_83_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_83_);
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
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_a_73_);
lean_del_object(v___x_70_);
lean_dec(v_mvarId_68_);
lean_dec_ref(v_toGoalState_67_);
v_a_104_ = lean_ctor_get(v___x_75_, 0);
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
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
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
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_del_object(v___x_70_);
lean_dec(v_mvarId_68_);
lean_dec_ref(v_toGoalState_67_);
v_a_112_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_72_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_72_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_65_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_65_);
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
else
{
return v___x_64_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_55_ = stack[0].m_obj;
lean_object* v___y_56_ = stack[1].m_obj;
lean_object* v___y_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v___y_59_ = stack[4].m_obj;
lean_object* v___y_60_ = stack[5].m_obj;
lean_object* v___y_61_ = stack[6].m_obj;
lean_object* v___y_62_ = stack[7].m_obj;
lean_object* v_res_129_;
v_res_129_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___boxed(lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_139_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___f_150_; lean_object* v___x_151_; 
v___f_150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0));
v___x_151_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_150_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_151_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_141_ = stack[0].m_obj;
lean_object* v_a_142_ = stack[1].m_obj;
lean_object* v_a_143_ = stack[2].m_obj;
lean_object* v_a_144_ = stack[3].m_obj;
lean_object* v_a_145_ = stack[4].m_obj;
lean_object* v_a_146_ = stack[5].m_obj;
lean_object* v_a_147_ = stack[6].m_obj;
lean_object* v_a_148_ = stack[7].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___boxed(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_162_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_173_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_163_ = stack[0].m_obj;
lean_object* v_a_164_ = stack[1].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
lean_object* v_a_166_ = stack[3].m_obj;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_a_168_ = stack[5].m_obj;
lean_object* v_a_169_ = stack[6].m_obj;
lean_object* v_a_170_ = stack[7].m_obj;
lean_object* v_a_171_ = stack[8].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(v_x_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(v_x_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_x_175_);
return v_res_185_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(lean_object* v_00_u03b1_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_187_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_187_ = stack[1].m_obj;
lean_object* v___y_188_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[3].m_obj;
lean_object* v___y_190_ = stack[4].m_obj;
lean_object* v___y_191_ = stack[5].m_obj;
lean_object* v___y_192_ = stack[6].m_obj;
lean_object* v___y_193_ = stack[7].m_obj;
lean_object* v___y_194_ = stack[8].m_obj;
lean_object* v___y_195_ = stack[9].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(lean_box(0), v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___boxed(lean_object* v_00_u03b1_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(v_00_u03b1_199_, v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_210_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1(){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5));
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21));
v___x_266_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed), 10, 0);
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_263_, v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_268_;
v_res_268_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___boxed(lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
return v_res_270_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
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
