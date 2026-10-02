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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0(lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_51_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v___x_61_; 
lean_dec_ref_known(v___x_60_, 1);
v___x_61_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_52_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v_toGoalState_63_; lean_object* v_mvarId_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_116_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_61_, 1);
v_toGoalState_63_ = lean_ctor_get(v_a_62_, 0);
v_mvarId_64_ = lean_ctor_get(v_a_62_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_116_ == 0)
{
v___x_66_ = v_a_62_;
v_isShared_67_ = v_isSharedCheck_116_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_mvarId_64_);
lean_inc(v_toGoalState_63_);
lean_dec(v_a_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_116_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; 
lean_inc(v_mvarId_64_);
v___x_68_ = l_Lean_MVarId_getType(v_mvarId_64_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_n(v_a_69_, 2);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_liftLets___boxed), 8, 1);
lean_closure_set(v___x_70_, 0, v_a_69_);
v___x_71_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_70_, v___y_51_, v___y_52_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; size_t v___x_95_; size_t v___x_96_; uint8_t v___x_97_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_95_ = lean_ptr_addr(v_a_69_);
lean_dec(v_a_69_);
v___x_96_ = lean_ptr_addr(v_a_72_);
v___x_97_ = lean_usize_dec_eq(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
v___y_74_ = v___y_52_;
v___y_75_ = v___y_55_;
v___y_76_ = v___y_56_;
v___y_77_ = v___y_57_;
v___y_78_ = v___y_58_;
goto v___jp_73_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_a_72_);
lean_del_object(v___x_66_);
lean_dec(v_mvarId_64_);
lean_dec_ref(v_toGoalState_63_);
v___x_98_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___closed__1);
v___x_99_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v___x_98_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
return v___x_99_;
}
v___jp_73_:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_64_, v_a_72_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v_a_80_);
v___x_82_ = v___x_66_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_toGoalState_63_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_a_80_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_84_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
return v___x_85_;
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_del_object(v___x_66_);
lean_dec_ref(v_toGoalState_63_);
v_a_87_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_79_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_79_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec(v_a_69_);
lean_del_object(v___x_66_);
lean_dec(v_mvarId_64_);
lean_dec_ref(v_toGoalState_63_);
v_a_100_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_71_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_71_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_del_object(v___x_66_);
lean_dec(v_mvarId_64_);
lean_dec_ref(v_toGoalState_63_);
v_a_108_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_68_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_68_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_61_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_61_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
else
{
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0___boxed(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___lam__0(v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___f_145_; lean_object* v___x_146_; 
v___f_145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___closed__0));
v___x_146_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_145_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg___boxed(lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets(lean_object* v_x_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___redArg(v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___boxed(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets(v_x_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_x_168_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0(lean_object* v_00_u03b1_179_, lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___redArg(v_msg_180_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0___boxed(lean_object* v_00_u03b1_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets_spec__0(v_00_u03b1_191_, v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1(){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__5));
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___closed__21));
v___x_258_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___boxed), 10, 0);
v___x_259_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_255_, v___x_256_, v___x_257_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1___boxed(lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets___regBuiltin___private_Lean_Elab_Tactic_Grind_LiftLet_0__Lean_Elab_Tactic_Grind_evalSymLiftLets__1();
return v_res_261_;
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
