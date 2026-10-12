// Lean compiler output
// Module: Lean.Elab.Tactic.Show
// Imports: public import Lean.Elab.Tactic.Change
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`show` tactic failed, pattern"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nis not definitionally equal to target"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "`show` tactic failed, no goals unify with the given pattern.\n\nIn the first goal, the pattern"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "\nis not definitionally equal to the target"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "\n(Errors for other goals omitted)"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "show"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 206, 21, 45, 142, 244, 84, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabShow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabShow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalShow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalShow___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalShow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalShow___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalShow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalShow___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalShow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 147, 62, 103, 130, 224, 84, 63)}};
static const lean_object* l_Lean_Elab_Tactic_evalShow___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalShow"};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalShow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 123, 168, 13, 212, 9, 86, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___boxed(lean_object*);
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2));
v___x_6_ = l_Lean_stringToMessageData(v___x_5_);
return v___x_6_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(lean_object* v_p_7_, lean_object* v_tgt_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_10_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1, &l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1);
v___x_11_ = l_Lean_indentExpr(v_p_7_);
v___x_12_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
v___x_13_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3, &l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3);
v___x_14_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = l_Lean_indentExpr(v_tgt_8_);
v___x_16_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_7_ = stack[0].m_obj;
lean_object* v_tgt_8_ = stack[1].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(v_p_7_, v_tgt_8_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___boxed(lean_object* v_p_19_, lean_object* v_tgt_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(v_p_19_, v_tgt_20_);
return v_res_22_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(lean_object* v_p_23_, lean_object* v_tgt_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(v_p_23_, v_tgt_24_);
return v___x_30_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_23_ = stack[0].m_obj;
lean_object* v_tgt_24_ = stack[1].m_obj;
lean_object* v_a_25_ = stack[2].m_obj;
lean_object* v_a_26_ = stack[3].m_obj;
lean_object* v_a_27_ = stack[4].m_obj;
lean_object* v_a_28_ = stack[5].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(v_p_23_, v_tgt_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(lean_object* v_p_32_, lean_object* v_tgt_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(v_p_32_, v_tgt_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0));
v___x_42_ = l_Lean_stringToMessageData(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2));
v___x_45_ = l_Lean_stringToMessageData(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4));
v___x_48_ = l_Lean_stringToMessageData(v___x_47_);
return v___x_48_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(lean_object* v_p_49_, lean_object* v_tgt_50_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_52_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1, &l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1);
v___x_53_ = l_Lean_indentExpr(v_p_49_);
v___x_54_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3, &l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = l_Lean_indentExpr(v_tgt_50_);
v___x_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5, &l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5);
v___x_60_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_49_ = stack[0].m_obj;
lean_object* v_tgt_50_ = stack[1].m_obj;
lean_object* v_res_62_;
v_res_62_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(v_p_49_, v_tgt_50_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___boxed(lean_object* v_p_63_, lean_object* v_tgt_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(v_p_63_, v_tgt_64_);
return v_res_66_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(lean_object* v_p_67_, lean_object* v_tgt_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(v_p_67_, v_tgt_68_);
return v___x_74_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_67_ = stack[0].m_obj;
lean_object* v_tgt_68_ = stack[1].m_obj;
lean_object* v_a_69_ = stack[2].m_obj;
lean_object* v_a_70_ = stack[3].m_obj;
lean_object* v_a_71_ = stack[4].m_obj;
lean_object* v_a_72_ = stack[5].m_obj;
lean_object* v_res_75_;
v_res_75_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(v_p_67_, v_tgt_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(lean_object* v_p_76_, lean_object* v_tgt_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(v_p_76_, v_tgt_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_83_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_94_ = lean_apply_9(v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, lean_box(0));
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_84_ = stack[0].m_obj;
lean_object* v___y_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_106_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(lean_object* v_mvarId_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; 
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
v___f_118_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_118_, 0, v_x_108_);
lean_closure_set(v___f_118_, 1, v___y_109_);
lean_closure_set(v___f_118_, 2, v___y_110_);
lean_closure_set(v___f_118_, 3, v___y_111_);
lean_closure_set(v___f_118_, 4, v___y_112_);
v___x_119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_107_, v___f_118_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
return v___x_119_;
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_107_ = stack[0].m_obj;
lean_object* v_x_108_ = stack[1].m_obj;
lean_object* v___y_109_ = stack[2].m_obj;
lean_object* v___y_110_ = stack[3].m_obj;
lean_object* v___y_111_ = stack[4].m_obj;
lean_object* v___y_112_ = stack[5].m_obj;
lean_object* v___y_113_ = stack[6].m_obj;
lean_object* v___y_114_ = stack[7].m_obj;
lean_object* v___y_115_ = stack[8].m_obj;
lean_object* v___y_116_ = stack[9].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_107_, v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___boxed(lean_object* v_mvarId_129_, lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_129_, v_x_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_140_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(lean_object* v_00_u03b1_141_, lean_object* v_mvarId_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_142_, v_x_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_142_ = stack[1].m_obj;
lean_object* v_x_143_ = stack[2].m_obj;
lean_object* v___y_144_ = stack[3].m_obj;
lean_object* v___y_145_ = stack[4].m_obj;
lean_object* v___y_146_ = stack[5].m_obj;
lean_object* v___y_147_ = stack[6].m_obj;
lean_object* v___y_148_ = stack[7].m_obj;
lean_object* v___y_149_ = stack[8].m_obj;
lean_object* v___y_150_ = stack[9].m_obj;
lean_object* v___y_151_ = stack[10].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(lean_box(0), v_mvarId_142_, v_x_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___boxed(lean_object* v_00_u03b1_155_, lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(v_00_u03b1_155_, v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_167_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(lean_object* v___x_168_, lean_object* v_a_169_, lean_object* v___x_170_, uint8_t v___x_171_, lean_object* v_goal_172_, lean_object* v_goals_173_, lean_object* v_prevRev_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_168_, v_a_169_, v___x_170_, v___x_171_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_207_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v_fst_186_ = lean_ctor_get(v_a_185_, 0);
v_snd_187_ = lean_ctor_get(v_a_185_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_189_ = v_a_185_;
v_isShared_190_ = v_isSharedCheck_207_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snd_187_);
lean_inc(v_fst_186_);
lean_dec(v_a_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_207_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_172_, v_fst_186_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l_List_appendTR___redArg(v_snd_187_, v_goals_173_);
v___x_194_ = l_List_reverseAux___redArg(v_prevRev_174_, v___x_193_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 1, v___x_194_);
lean_ctor_set(v___x_189_, 0, v_a_192_);
v___x_196_ = v___x_189_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_196_, v___y_176_);
return v___x_197_;
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_189_);
lean_dec(v_snd_187_);
lean_dec(v_prevRev_174_);
lean_dec(v_goals_173_);
v_a_199_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_191_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_191_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_prevRev_174_);
lean_dec(v_goals_173_);
lean_dec(v_goal_172_);
v_a_208_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_184_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_184_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_168_ = stack[0].m_obj;
lean_object* v_a_169_ = stack[1].m_obj;
lean_object* v___x_170_ = stack[2].m_obj;
uint8_t v___x_171_ = stack[3].m_num;
lean_object* v_goal_172_ = stack[4].m_obj;
lean_object* v_goals_173_ = stack[5].m_obj;
lean_object* v_prevRev_174_ = stack[6].m_obj;
lean_object* v___y_175_ = stack[7].m_obj;
lean_object* v___y_176_ = stack[8].m_obj;
lean_object* v___y_177_ = stack[9].m_obj;
lean_object* v___y_178_ = stack[10].m_obj;
lean_object* v___y_179_ = stack[11].m_obj;
lean_object* v___y_180_ = stack[12].m_obj;
lean_object* v___y_181_ = stack[13].m_obj;
lean_object* v___y_182_ = stack[14].m_obj;
lean_object* v_res_216_;
v_res_216_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(v___x_168_, v_a_169_, v___x_170_, v___x_171_, v_goal_172_, v_goals_173_, v_prevRev_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed(lean_object* v___x_217_, lean_object* v_a_218_, lean_object* v___x_219_, lean_object* v___x_220_, lean_object* v_goal_221_, lean_object* v_goals_222_, lean_object* v_prevRev_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v___x_2332__boxed_233_; lean_object* v_res_234_; 
v___x_2332__boxed_233_ = lean_unbox(v___x_220_);
v_res_234_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(v___x_217_, v_a_218_, v___x_219_, v___x_2332__boxed_233_, v_goal_221_, v_goals_222_, v_prevRev_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_234_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(lean_object* v_newType_238_, lean_object* v_goal_239_, lean_object* v_goals_240_, lean_object* v_prevRev_241_, lean_object* v_err_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; 
lean_inc(v_goal_239_);
v___x_252_ = l_Lean_MVarId_getType(v_goal_239_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
lean_inc(v_goal_239_);
v___x_254_ = l_Lean_MVarId_getTag(v_goal_239_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___boxed), 12, 3);
lean_closure_set(v___x_256_, 0, v_a_253_);
lean_closure_set(v___x_256_, 1, v_newType_238_);
lean_closure_set(v___x_256_, 2, v_err_242_);
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1));
v___x_258_ = 0;
v___x_259_ = lean_box(v___x_258_);
lean_inc(v_goal_239_);
v___f_260_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed), 16, 7);
lean_closure_set(v___f_260_, 0, v___x_256_);
lean_closure_set(v___f_260_, 1, v_a_255_);
lean_closure_set(v___f_260_, 2, v___x_257_);
lean_closure_set(v___f_260_, 3, v___x_259_);
lean_closure_set(v___f_260_, 4, v_goal_239_);
lean_closure_set(v___f_260_, 5, v_goals_240_);
lean_closure_set(v___f_260_, 6, v_prevRev_241_);
v___x_261_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_goal_239_, v___f_260_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
return v___x_261_;
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_a_253_);
lean_dec_ref(v_err_242_);
lean_dec(v_prevRev_241_);
lean_dec(v_goals_240_);
lean_dec(v_goal_239_);
lean_dec(v_newType_238_);
v_a_262_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_254_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_254_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_err_242_);
lean_dec(v_prevRev_241_);
lean_dec(v_goals_240_);
lean_dec(v_goal_239_);
lean_dec(v_newType_238_);
v_a_270_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_252_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_252_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_newType_238_ = stack[0].m_obj;
lean_object* v_goal_239_ = stack[1].m_obj;
lean_object* v_goals_240_ = stack[2].m_obj;
lean_object* v_prevRev_241_ = stack[3].m_obj;
lean_object* v_err_242_ = stack[4].m_obj;
lean_object* v_a_243_ = stack[5].m_obj;
lean_object* v_a_244_ = stack[6].m_obj;
lean_object* v_a_245_ = stack[7].m_obj;
lean_object* v_a_246_ = stack[8].m_obj;
lean_object* v_a_247_ = stack[9].m_obj;
lean_object* v_a_248_ = stack[10].m_obj;
lean_object* v_a_249_ = stack[11].m_obj;
lean_object* v_a_250_ = stack[12].m_obj;
lean_object* v_res_278_;
v_res_278_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(v_newType_238_, v_goal_239_, v_goals_240_, v_prevRev_241_, v_err_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed(lean_object* v_newType_279_, lean_object* v_goal_280_, lean_object* v_goals_281_, lean_object* v_prevRev_282_, lean_object* v_err_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(v_newType_279_, v_goal_280_, v_goals_281_, v_prevRev_282_, v_err_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
return v_res_293_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(lean_object* v_newType_296_, lean_object* v_firstGoal_297_, lean_object* v_goals_298_, lean_object* v_prevRev_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
if (lean_obj_tag(v_goals_298_) == 0)
{
lean_object* v___x_309_; 
lean_dec(v_prevRev_299_);
v___x_309_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_301_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___y_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
if (lean_obj_tag(v_a_310_) == 0)
{
v___y_312_ = v_a_310_;
goto v___jp_311_;
}
else
{
lean_object* v_tail_315_; 
v_tail_315_ = lean_ctor_get(v_a_310_, 1);
lean_inc(v_tail_315_);
lean_dec_ref_known(v_a_310_, 2);
v___y_312_ = v_tail_315_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0));
v___x_314_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(v_newType_296_, v_firstGoal_297_, v___y_312_, v_goals_298_, v___x_313_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
return v___x_314_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_firstGoal_297_);
lean_dec(v_newType_296_);
v_a_316_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_309_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_309_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_head_324_; lean_object* v_tail_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_363_; 
v_head_324_ = lean_ctor_get(v_goals_298_, 0);
v_tail_325_ = lean_ctor_get(v_goals_298_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_goals_298_);
if (v_isSharedCheck_363_ == 0)
{
v___x_327_ = v_goals_298_;
v_isShared_328_ = v_isSharedCheck_363_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_tail_325_);
lean_inc(v_head_324_);
lean_dec(v_goals_298_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_363_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; uint8_t v___y_333_; uint8_t v___y_340_; uint8_t v___x_360_; 
v___x_360_ = l_List_isEmpty___redArg(v_tail_325_);
if (v___x_360_ == 0)
{
v___y_340_ = v___x_360_;
goto v___jp_339_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = l_List_isEmpty___redArg(v_prevRev_299_);
if (v___x_361_ == 0)
{
uint8_t v_recover_362_; 
v_recover_362_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*1);
if (v_recover_362_ == 0)
{
v___y_340_ = v___x_360_;
goto v___jp_339_;
}
else
{
v___y_340_ = v___x_361_;
goto v___jp_339_;
}
}
else
{
v___y_340_ = v___x_361_;
goto v___jp_339_;
}
}
v___jp_329_:
{
if (v___y_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec_ref(v___y_332_);
v___x_334_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_331_, v___y_330_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_336_; 
lean_dec_ref_known(v___x_334_, 1);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_prevRev_299_);
v___x_336_ = v___x_327_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_head_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_prevRev_299_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v_goals_298_ = v_tail_325_;
v_prevRev_299_ = v___x_336_;
goto _start;
}
}
else
{
lean_del_object(v___x_327_);
lean_dec(v_tail_325_);
lean_dec(v_head_324_);
lean_dec(v_prevRev_299_);
lean_dec(v_firstGoal_297_);
lean_dec(v_newType_296_);
return v___x_334_;
}
}
else
{
lean_dec_ref(v___y_331_);
lean_del_object(v___x_327_);
lean_dec(v_tail_325_);
lean_dec(v_head_324_);
lean_dec(v_prevRev_299_);
lean_dec(v_firstGoal_297_);
lean_dec(v_newType_296_);
return v___y_332_;
}
}
v___jp_339_:
{
if (v___y_340_ == 0)
{
uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_341_ = 1;
v___x_342_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_301_, v_a_303_, v_a_305_, v_a_307_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1));
lean_inc(v_prevRev_299_);
lean_inc(v_tail_325_);
lean_inc(v_head_324_);
lean_inc(v_newType_296_);
v___x_345_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed), 14, 5);
lean_closure_set(v___x_345_, 0, v_newType_296_);
lean_closure_set(v___x_345_, 1, v_head_324_);
lean_closure_set(v___x_345_, 2, v_tail_325_);
lean_closure_set(v___x_345_, 3, v_prevRev_299_);
lean_closure_set(v___x_345_, 4, v___x_344_);
v___x_346_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_345_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec(v_a_343_);
lean_del_object(v___x_327_);
lean_dec(v_tail_325_);
lean_dec(v_head_324_);
lean_dec(v_prevRev_299_);
lean_dec(v_firstGoal_297_);
lean_dec(v_newType_296_);
return v___x_346_;
}
else
{
lean_object* v_a_347_; uint8_t v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v___x_348_ = l_Lean_Exception_isInterrupt(v_a_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; 
lean_inc(v_a_347_);
v___x_349_ = l_Lean_Exception_isRuntime(v_a_347_);
v___y_330_ = v___x_341_;
v___y_331_ = v_a_343_;
v___y_332_ = v___x_346_;
v___y_333_ = v___x_349_;
goto v___jp_329_;
}
else
{
v___y_330_ = v___x_341_;
v___y_331_ = v_a_343_;
v___y_332_ = v___x_346_;
v___y_333_ = v___x_348_;
goto v___jp_329_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_del_object(v___x_327_);
lean_dec(v_tail_325_);
lean_dec(v_head_324_);
lean_dec(v_prevRev_299_);
lean_dec(v_firstGoal_297_);
lean_dec(v_newType_296_);
v_a_350_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_342_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_342_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_del_object(v___x_327_);
lean_dec(v_firstGoal_297_);
v___x_358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1));
v___x_359_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(v_newType_296_, v_head_324_, v_tail_325_, v_prevRev_299_, v___x_358_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_newType_296_ = stack[0].m_obj;
lean_object* v_firstGoal_297_ = stack[1].m_obj;
lean_object* v_goals_298_ = stack[2].m_obj;
lean_object* v_prevRev_299_ = stack[3].m_obj;
lean_object* v_a_300_ = stack[4].m_obj;
lean_object* v_a_301_ = stack[5].m_obj;
lean_object* v_a_302_ = stack[6].m_obj;
lean_object* v_a_303_ = stack[7].m_obj;
lean_object* v_a_304_ = stack[8].m_obj;
lean_object* v_a_305_ = stack[9].m_obj;
lean_object* v_a_306_ = stack[10].m_obj;
lean_object* v_a_307_ = stack[11].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(v_newType_296_, v_firstGoal_297_, v_goals_298_, v_prevRev_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___boxed(lean_object* v_newType_365_, lean_object* v_firstGoal_366_, lean_object* v_goals_367_, lean_object* v_prevRev_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(v_newType_365_, v_firstGoal_366_, v_goals_367_, v_prevRev_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_378_;
}
}
lean_object* l_Lean_Elab_Tactic_elabShow(lean_object* v_newType_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_381_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
if (lean_obj_tag(v_a_390_) == 1)
{
lean_object* v_head_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_head_391_ = lean_ctor_get(v_a_390_, 0);
lean_inc(v_head_391_);
v___x_392_ = lean_box(0);
v___x_393_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(v_newType_379_, v_head_391_, v_a_390_, v___x_392_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; 
lean_dec(v_a_390_);
lean_dec(v_newType_379_);
v___x_394_ = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_394_;
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_newType_379_);
v_a_395_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabShow_0interp(lean_interpreter_value* stack)
{
lean_object* v_newType_379_ = stack[0].m_obj;
lean_object* v_a_380_ = stack[1].m_obj;
lean_object* v_a_381_ = stack[2].m_obj;
lean_object* v_a_382_ = stack[3].m_obj;
lean_object* v_a_383_ = stack[4].m_obj;
lean_object* v_a_384_ = stack[5].m_obj;
lean_object* v_a_385_ = stack[6].m_obj;
lean_object* v_a_386_ = stack[7].m_obj;
lean_object* v_a_387_ = stack[8].m_obj;
lean_object* v_res_403_;
v_res_403_ = l_Lean_Elab_Tactic_elabShow(v_newType_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabShow___boxed(lean_object* v_newType_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Tactic_elabShow(v_newType_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_414_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
return v___x_417_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_421_;
v_res_421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___boxed(lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
return v_res_423_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(lean_object* v_00_u03b1_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
return v___x_434_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_425_ = stack[1].m_obj;
lean_object* v___y_426_ = stack[2].m_obj;
lean_object* v___y_427_ = stack[3].m_obj;
lean_object* v___y_428_ = stack[4].m_obj;
lean_object* v___y_429_ = stack[5].m_obj;
lean_object* v___y_430_ = stack[6].m_obj;
lean_object* v___y_431_ = stack[7].m_obj;
lean_object* v___y_432_ = stack[8].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(lean_box(0), v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___boxed(lean_object* v_00_u03b1_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(v_00_u03b1_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_446_;
}
}
lean_object* l_Lean_Elab_Tactic_evalShow(lean_object* v_x_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Elab_Tactic_evalShow___closed__3));
lean_inc(v_x_455_);
v___x_466_ = l_Lean_Syntax_isOfKind(v_x_455_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec(v_x_455_);
v___x_467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v_newType_469_; lean_object* v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v_newType_469_ = l_Lean_Syntax_getArg(v_x_455_, v___x_468_);
lean_dec(v_x_455_);
v___x_470_ = l_Lean_Elab_Tactic_elabShow(v_newType_469_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
return v___x_470_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalShow_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_455_ = stack[0].m_obj;
lean_object* v_a_456_ = stack[1].m_obj;
lean_object* v_a_457_ = stack[2].m_obj;
lean_object* v_a_458_ = stack[3].m_obj;
lean_object* v_a_459_ = stack[4].m_obj;
lean_object* v_a_460_ = stack[5].m_obj;
lean_object* v_a_461_ = stack[6].m_obj;
lean_object* v_a_462_ = stack[7].m_obj;
lean_object* v_a_463_ = stack[8].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_Lean_Elab_Tactic_evalShow(v_x_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalShow___boxed(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Tactic_evalShow(v_x_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_482_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1(){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_evalShow___closed__3));
v___x_493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2));
v___x_494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalShow___boxed), 10, 0);
v___x_495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_491_, v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_496_;
v_res_496_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
return v_res_498_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Change(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Show(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Show(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Show(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Show(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Show(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Show(builtin);
}
#ifdef __cplusplus
}
#endif
