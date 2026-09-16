// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.LiftLet
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Sym.LiftLet import Lean.Meta.Tactic.Replace
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
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`lift_lets` made no progress"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symLiftLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 83, 69, 73, 55, 43, 139, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LiftLet"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 217, 135, 204, 13, 136, 125, 5)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(143, 16, 99, 112, 22, 9, 95, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 83, 46, 240, 194, 136, 178, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(128, 221, 102, 11, 225, 120, 84, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__17_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 241, 205, 74, 201, 64, 88, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 92, 55, 119, 250, 197, 205, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalSymLiftLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(122, 217, 194, 141, 99, 98, 58, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0(lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_50_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v___x_60_; 
lean_dec_ref_known(v___x_59_, 1);
v___x_60_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_51_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_toGoalState_62_; lean_object* v_mvarId_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_115_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v_toGoalState_62_ = lean_ctor_get(v_a_61_, 0);
v_mvarId_63_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_115_ == 0)
{
v___x_65_ = v_a_61_;
v_isShared_66_ = v_isSharedCheck_115_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_mvarId_63_);
lean_inc(v_toGoalState_62_);
lean_dec(v_a_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_115_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; 
lean_inc(v_mvarId_63_);
v___x_67_ = l_Lean_MVarId_getType(v_mvarId_63_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_n(v_a_68_, 2);
lean_dec_ref_known(v___x_67_, 1);
v___x_69_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLets___boxed), 8, 1);
lean_closure_set(v___x_69_, 0, v_a_68_);
v___x_70_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_69_, v___y_50_, v___y_51_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; size_t v___x_94_; size_t v___x_95_; uint8_t v___x_96_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_94_ = lean_ptr_addr(v_a_68_);
lean_dec(v_a_68_);
v___x_95_ = lean_ptr_addr(v_a_71_);
v___x_96_ = lean_usize_dec_eq(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
v___y_73_ = v___y_51_;
v___y_74_ = v___y_54_;
v___y_75_ = v___y_55_;
v___y_76_ = v___y_56_;
v___y_77_ = v___y_57_;
goto v___jp_72_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_a_71_);
lean_del_object(v___x_65_);
lean_dec(v_mvarId_63_);
lean_dec_ref(v_toGoalState_62_);
v___x_97_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1);
v___x_98_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v___x_97_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
return v___x_98_;
}
v___jp_72_:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_63_, v_a_71_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_a_79_);
v___x_81_ = v___x_65_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_toGoalState_62_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_a_79_);
v___x_81_ = v_reuseFailAlloc_85_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_83_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
return v___x_84_;
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_del_object(v___x_65_);
lean_dec_ref(v_toGoalState_62_);
v_a_86_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_78_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_78_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_mvarId_63_);
lean_dec_ref(v_toGoalState_62_);
v_a_99_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_70_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_70_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_del_object(v___x_65_);
lean_dec(v_mvarId_63_);
lean_dec_ref(v_toGoalState_62_);
v_a_107_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_67_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_67_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_a_116_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_60_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_60_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___boxed(lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0(v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; 
v___f_144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___closed__0));
v___x_145_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_144_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___boxed(lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___boxed(lean_object* v_x_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets(v_x_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_x_167_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v_msg_179_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___boxed(lean_object* v_00_u03b1_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0(v_00_u03b1_190_, v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1(){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_254_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5));
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__21));
v___x_257_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___boxed), 10, 0);
v___x_258_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_254_, v___x_255_, v___x_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___boxed(lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1();
return v_res_260_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LiftLet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LiftLet(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_LiftLet(builtin);
}
#ifdef __cplusplus
}
#endif
