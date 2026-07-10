// Lean compiler output
// Module: Lean.Elab.Tactic.ShowTerm
// Imports: public import Lean.Elab.ElabRules public import Lean.Meta.Tactic.TryThis
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTerm"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 168, 159, 5, 147, 101, 31, 84)}};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ShowTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 5, 182, 248, 23, 55, 41, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 123, 75, 48, 167, 48, 118, 50)}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "showTermElabImpl"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 231, 182, 51, 102, 120, 109, 161)}};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabShowTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 5, 182, 248, 23, 55, 41, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 201, 215, 219, 243, 98, 6, 88)}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Implementation of `show_term` term elaborator. "};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value),((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(lean_object* v_e_31_, lean_object* v___y_32_){
_start:
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
v___x_35_ = lean_bool_not(v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v_mctx_37_; lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; lean_object* v_cache_42_; lean_object* v_zetaDeltaFVarIds_43_; lean_object* v_postponed_44_; lean_object* v_diag_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v___x_36_ = lean_st_ref_get(v___y_32_);
v_mctx_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_mctx_37_);
lean_dec(v___x_36_);
v___x_38_ = l_Lean_instantiateMVarsCore(v_mctx_37_, v_e_31_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = lean_st_ref_take(v___y_32_);
v_cache_42_ = lean_ctor_get(v___x_41_, 1);
v_zetaDeltaFVarIds_43_ = lean_ctor_get(v___x_41_, 2);
v_postponed_44_ = lean_ctor_get(v___x_41_, 3);
v_diag_45_ = lean_ctor_get(v___x_41_, 4);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_55_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_diag_45_);
lean_inc(v_postponed_44_);
lean_inc(v_zetaDeltaFVarIds_43_);
lean_inc(v_cache_42_);
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v_snd_40_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_snd_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_cache_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_zetaDeltaFVarIds_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_postponed_44_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_diag_45_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_set(v___y_32_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fst_39_);
return v___x_52_;
}
}
}
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_e_31_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg___boxed(lean_object* v_e_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(v_e_57_, v___y_58_);
lean_dec(v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(lean_object* v_e_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(v_e_61_, v___y_67_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___boxed(lean_object* v_e_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(v_e_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(lean_object* v___x_83_, lean_object* v_tk_84_, uint8_t v___x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_87_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_87_, v___y_89_, v___y_91_, v___y_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = l_Lean_Elab_Tactic_evalTactic(v___x_83_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_121_; 
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_121_ == 0)
{
lean_object* v_unused_122_; 
v_unused_122_ = lean_ctor_get(v___x_99_, 0);
lean_dec(v_unused_122_);
v___x_101_ = v___x_99_;
v_isShared_102_ = v_isSharedCheck_121_;
goto v_resetjp_100_;
}
else
{
lean_dec(v___x_99_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_121_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_120_; 
v___x_103_ = l_Lean_mkMVar(v_a_96_);
v___x_104_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(v___x_103_, v___y_91_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_120_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_120_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_ref_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v_ref_109_ = lean_ctor_get(v___y_92_, 5);
v___x_110_ = l_Lean_Expr_headBeta(v_a_105_);
lean_inc(v_ref_109_);
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 1);
lean_ctor_set(v___x_107_, 0, v_ref_109_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_ref_109_);
v___x_112_ = v_reuseFailAlloc_119_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = 0;
v___x_114_ = lean_box(0);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 1);
lean_ctor_set(v___x_101_, 0, v_a_98_);
v___x_116_ = v___x_101_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_98_);
v___x_116_ = v_reuseFailAlloc_118_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_tk_84_, v___x_110_, v___x_112_, v___x_113_, v___x_114_, v___x_116_, v___x_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
return v___x_117_;
}
}
}
}
}
else
{
lean_dec(v_a_98_);
lean_dec(v_a_96_);
lean_dec(v_tk_84_);
return v___x_99_;
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_96_);
lean_dec(v_tk_84_);
lean_dec(v___x_83_);
v_a_123_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_97_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_97_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_tk_84_);
lean_dec(v___x_83_);
v_a_131_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_95_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_95_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed(lean_object* v___x_139_, lean_object* v_tk_140_, lean_object* v___x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v___x_2256__boxed_151_; lean_object* v_res_152_; 
v___x_2256__boxed_151_ = lean_unbox(v___x_141_);
v_res_152_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(v___x_139_, v_tk_140_, v___x_2256__boxed_151_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(lean_object* v_stx_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4));
lean_inc(v_stx_162_);
v___x_173_ = l_Lean_Syntax_isOfKind(v_stx_162_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_dec(v_stx_162_);
v___x_174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v_tk_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v_tk_176_ = l_Lean_Syntax_getArg(v_stx_162_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = l_Lean_Syntax_getArg(v_stx_162_, v___x_177_);
lean_dec(v_stx_162_);
v___x_179_ = lean_box(v___x_173_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed), 12, 3);
lean_closure_set(v___f_180_, 0, v___x_178_);
lean_closure_set(v___f_180_, 1, v_tk_176_);
lean_closure_set(v___f_180_, 2, v___x_179_);
v___x_181_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_180_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed(lean_object* v_stx_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(v_stx_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1(){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_203_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_204_ = ((lean_object*)(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4));
v___x_205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3));
v___x_206_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed), 10, 0);
v___x_207_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_203_, v___x_204_, v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3(){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3));
v___x_237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6));
v___x_238_ = l_Lean_addBuiltinDeclarationRanges(v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg___boxed(lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(lean_object* v_00_u03b1_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(v_00_u03b1_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(lean_object* v_e_264_, lean_object* v___y_265_){
_start:
{
uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = l_Lean_Expr_hasMVar(v_e_264_);
v___x_268_ = lean_bool_not(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v_mctx_270_; lean_object* v___x_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_274_; lean_object* v_cache_275_; lean_object* v_zetaDeltaFVarIds_276_; lean_object* v_postponed_277_; lean_object* v_diag_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_287_; 
v___x_269_ = lean_st_ref_get(v___y_265_);
v_mctx_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_mctx_270_);
lean_dec(v___x_269_);
v___x_271_ = l_Lean_instantiateMVarsCore(v_mctx_270_, v_e_264_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v___x_271_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v___x_271_);
v___x_274_ = lean_st_ref_take(v___y_265_);
v_cache_275_ = lean_ctor_get(v___x_274_, 1);
v_zetaDeltaFVarIds_276_ = lean_ctor_get(v___x_274_, 2);
v_postponed_277_ = lean_ctor_get(v___x_274_, 3);
v_diag_278_ = lean_ctor_get(v___x_274_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_288_);
v___x_280_ = v___x_274_;
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_diag_278_);
lean_inc(v_postponed_277_);
lean_inc(v_zetaDeltaFVarIds_276_);
lean_inc(v_cache_275_);
lean_dec(v___x_274_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v_snd_273_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_snd_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_cache_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_zetaDeltaFVarIds_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_postponed_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_diag_278_);
v___x_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_st_ref_set(v___y_265_, v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_fst_272_);
return v___x_285_;
}
}
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v_e_264_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg___boxed(lean_object* v_e_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(v_e_290_, v___y_291_);
lean_dec(v___y_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(lean_object* v_e_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(v_e_294_, v___y_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___boxed(lean_object* v_e_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(v_e_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2));
lean_inc(v_x_320_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_x_320_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_x_321_);
lean_dec(v_x_320_);
v___x_331_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = l_Lean_Syntax_getArg(v_x_320_, v___x_332_);
v___x_334_ = lean_box(0);
v___x_335_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_333_, v_x_321_, v___x_330_, v___x_330_, v___x_334_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = 0;
v___x_338_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_337_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref_known(v___x_338_, 1);
lean_inc(v_a_336_);
v___x_339_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(v_a_336_, v_a_325_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_369_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_369_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_369_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_ref_344_; lean_object* v___x_345_; lean_object* v_tk_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v_ref_344_ = lean_ctor_get(v_a_326_, 5);
v___x_345_ = lean_unsigned_to_nat(0u);
v_tk_346_ = l_Lean_Syntax_getArg(v_x_320_, v___x_345_);
lean_dec(v_x_320_);
v___x_347_ = l_Lean_Expr_headBeta(v_a_340_);
lean_inc(v_ref_344_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 1);
lean_ctor_set(v___x_342_, 0, v_ref_344_);
v___x_349_ = v___x_342_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_ref_344_);
v___x_349_ = v_reuseFailAlloc_368_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3));
v___x_351_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_tk_346_, v___x_347_, v___x_349_, v___x_350_, v___x_334_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_359_);
v___x_353_ = v___x_351_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_dec(v___x_351_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v_a_336_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_336_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_a_336_);
v_a_360_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_a_336_);
lean_dec(v_x_320_);
v_a_370_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_338_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_338_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_dec(v_x_320_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(v_x_378_, v_x_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1(){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_396_ = l_Lean_Elab_Term_termElabAttribute;
v___x_397_ = ((lean_object*)(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2));
v___x_398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1));
v___x_399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___boxed), 9, 0);
v___x_400_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_396_, v___x_397_, v___x_398_, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___boxed(lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3(){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1));
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0));
v___x_407_ = l_Lean_addBuiltinDocString(v___x_405_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___boxed(lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5(){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1));
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6));
v___x_438_ = l_Lean_addBuiltinDeclarationRanges(v___x_436_, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___boxed(lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
return v_res_440_;
}
}
lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_ShowTerm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_ShowTerm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ShowTerm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_ShowTerm(builtin);
}
#ifdef __cplusplus
}
#endif
