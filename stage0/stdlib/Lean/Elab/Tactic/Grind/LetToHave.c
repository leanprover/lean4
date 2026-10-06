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
lean_object* v_a_64_; lean_object* v_toGoalState_65_; lean_object* v_mvarId_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_118_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
v_toGoalState_65_ = lean_ctor_get(v_a_64_, 0);
v_mvarId_66_ = lean_ctor_get(v_a_64_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_118_ == 0)
{
v___x_68_ = v_a_64_;
v_isShared_69_ = v_isSharedCheck_118_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_mvarId_66_);
lean_inc(v_toGoalState_65_);
lean_dec(v_a_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_118_;
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
lean_inc_n(v_a_71_, 2);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___boxed), 8, 1);
lean_closure_set(v___x_72_, 0, v_a_71_);
v___x_73_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_72_, v___y_53_, v___y_54_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; size_t v___x_97_; size_t v___x_98_; uint8_t v___x_99_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_73_, 1);
v___x_97_ = lean_ptr_addr(v_a_71_);
lean_dec(v_a_71_);
v___x_98_ = lean_ptr_addr(v_a_74_);
v___x_99_ = lean_usize_dec_eq(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
v___y_76_ = v___y_54_;
v___y_77_ = v___y_57_;
v___y_78_ = v___y_58_;
v___y_79_ = v___y_59_;
v___y_80_ = v___y_60_;
goto v___jp_75_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_a_74_);
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v___x_100_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___closed__1);
v___x_101_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v___x_100_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
return v___x_101_;
}
v___jp_75_:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_66_, v_a_74_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_a_82_);
v___x_84_ = v___x_68_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_toGoalState_65_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_a_82_);
v___x_84_ = v_reuseFailAlloc_88_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_86_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
return v___x_87_;
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_del_object(v___x_68_);
lean_dec_ref(v_toGoalState_65_);
v_a_89_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_81_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_81_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_71_);
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v_a_102_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_73_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_73_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_del_object(v___x_68_);
lean_dec(v_mvarId_66_);
lean_dec_ref(v_toGoalState_65_);
v_a_110_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_70_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_70_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_63_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_63_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0___boxed(lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___lam__0(v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; 
v___f_147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___closed__0));
v___x_148_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_147_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg___boxed(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___redArg(v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave(v_x_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_x_170_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(lean_object* v_00_u03b1_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___redArg(v_msg_182_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0___boxed(lean_object* v_00_u03b1_193_, lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave_spec__0(v_00_u03b1_193_, v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1(){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__5));
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___closed__21));
v___x_260_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___boxed), 10, 0);
v___x_261_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_257_, v___x_258_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1___boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave___regBuiltin___private_Lean_Elab_Tactic_Grind_LetToHave_0__Lean_Elab_Tactic_Grind_evalSymLetToHave__1();
return v_res_263_;
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
