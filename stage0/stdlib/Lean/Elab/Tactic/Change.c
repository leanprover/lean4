// Lean compiler output
// Module: Lean.Elab.Tactic.Change
// Imports: public import Lean.Meta.Tactic.Replace public import Lean.Elab.Tactic.Location
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "'change' tactic failed, pattern"};
static const lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nis not definitionally equal to target"};
static const lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalChange___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "`change` tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalChange___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalChange___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabChangeDefaultError___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalChange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalChange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalChange___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalChange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 221, 63, 213, 180, 29, 27, 230)}};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalChange___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalChange___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalChange___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalChange___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Elab_Tactic_evalChange___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalChange"};
static const lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalChange___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(60, 128, 2, 217, 119, 234, 30, 147)}};
static const lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 757, .m_capacity = 757, .m_length = 752, .m_data = "`change` can be used to replace the main goal or its hypotheses with\ndifferent, yet definitionally equal, goal or hypotheses.\n\nFor example, if `n : Nat` and the current goal is `⊢ n + 2 = 2`, then\n```lean\nchange _ + 1 = _\n```\nchanges the goal to `⊢ n + 1 + 1 = 2`.\n\nThe tactic also applies to hypotheses. If `h : n + 2 = 2` and `h' : n + 3 = 4`\nare hypotheses, then\n```lean\nchange _ + 1 = _ at h h'\n```\nchanges their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.\n\nChange is like `refine` in that every placeholder needs to be solved for by unification,\nbut using named placeholders or `\?_` results in `change` to creating new goals.\n\nThe tactic `show e` is interchangeable with `change e`, where the pattern `e` is applied to\nthe main goal."};
static const lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2));
v___x_6_ = l_Lean_stringToMessageData(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(lean_object* v_p_7_, lean_object* v_tgt_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_10_ = lean_obj_once(&l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1, &l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1);
v___x_11_ = l_Lean_indentExpr(v_p_7_);
v___x_12_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
v___x_13_ = lean_obj_once(&l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3, &l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___boxed(lean_object* v_p_18_, lean_object* v_tgt_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_18_, v_tgt_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError(lean_object* v_p_22_, lean_object* v_tgt_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_22_, v_tgt_23_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___boxed(lean_object* v_p_30_, lean_object* v_tgt_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Tactic_elabChangeDefaultError(v_p_30_, v_tgt_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(lean_object* v_e_38_, lean_object* v___y_39_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_Expr_hasMVar(v_e_38_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v_e_38_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v_mctx_44_; lean_object* v___x_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_48_; lean_object* v_cache_49_; lean_object* v_zetaDeltaFVarIds_50_; lean_object* v_postponed_51_; lean_object* v_diag_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v___x_43_ = lean_st_ref_get(v___y_39_);
v_mctx_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_mctx_44_);
lean_dec(v___x_43_);
v___x_45_ = l_Lean_instantiateMVarsCore(v_mctx_44_, v_e_38_);
v_fst_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_fst_46_);
v_snd_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_snd_47_);
lean_dec_ref(v___x_45_);
v___x_48_ = lean_st_ref_take(v___y_39_);
v_cache_49_ = lean_ctor_get(v___x_48_, 1);
v_zetaDeltaFVarIds_50_ = lean_ctor_get(v___x_48_, 2);
v_postponed_51_ = lean_ctor_get(v___x_48_, 3);
v_diag_52_ = lean_ctor_get(v___x_48_, 4);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v___x_48_, 0);
lean_dec(v_unused_62_);
v___x_54_ = v___x_48_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_diag_52_);
lean_inc(v_postponed_51_);
lean_inc(v_zetaDeltaFVarIds_50_);
lean_inc(v_cache_49_);
lean_dec(v___x_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v_snd_47_);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_snd_47_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_cache_49_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_zetaDeltaFVarIds_50_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v_postponed_51_);
lean_ctor_set(v_reuseFailAlloc_60_, 4, v_diag_52_);
v___x_57_ = v_reuseFailAlloc_60_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_st_ref_put(v___y_39_, v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v_fst_46_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg___boxed(lean_object* v_e_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_e_63_, v___y_64_);
lean_dec(v___y_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(lean_object* v_e_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_e_67_, v___y_73_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___boxed(lean_object* v_e_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(v_e_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0(lean_object* v_e_89_, lean_object* v_p_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
lean_inc(v___y_96_);
lean_inc_ref(v___y_95_);
lean_inc(v___y_94_);
lean_inc_ref(v___y_93_);
lean_inc_ref(v_e_89_);
v___x_98_ = lean_infer_type(v_e_89_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_156_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_156_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_156_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_156_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 1);
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_155_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = 1;
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_Elab_Term_elabTermEnsuringType(v_p_90_, v___x_104_, v___x_105_, v___x_105_, v___x_106_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_n(v_a_108_, 2);
lean_dec_ref_known(v___x_107_, 1);
lean_inc_ref(v_e_89_);
v___x_109_ = l_Lean_Meta_isExprDefEq(v_a_108_, v_e_89_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_146_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_146_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_146_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_146_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = lean_unbox(v_a_110_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_112_);
v___x_115_ = 2;
v___x_116_ = lean_unbox(v_a_110_);
lean_dec(v_a_110_);
v___x_117_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_115_, v___x_116_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; 
lean_dec_ref_known(v___x_117_, 1);
lean_inc(v_a_108_);
v___x_118_ = l_Lean_Meta_isExprDefEq(v_a_108_, v_e_89_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v___x_118_, 0);
lean_dec(v_unused_126_);
v___x_120_ = v___x_118_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_dec(v___x_118_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_a_108_);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_108_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_a_108_);
v_a_127_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_118_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_118_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_a_108_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_e_89_);
v_a_135_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_117_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_117_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v___x_144_; 
lean_dec(v_a_110_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_e_89_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v_a_108_);
v___x_144_ = v___x_112_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_108_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_a_108_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_e_89_);
v_a_147_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_109_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_109_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_e_89_);
return v___x_107_;
}
}
}
}
else
{
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v_p_90_);
lean_dec_ref(v_e_89_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0___boxed(lean_object* v_e_157_, lean_object* v_p_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_Tactic_elabChange___lam__0(v_e_157_, v_p_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__1(lean_object* v___x_167_, lean_object* v_a_168_, lean_object* v_e_169_, lean_object* v_mkDefeqError_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
uint8_t v_trackZetaDelta_176_; lean_object* v_zetaDeltaSet_177_; lean_object* v_lctx_178_; lean_object* v_localInstances_179_; lean_object* v_defEqCtx_x3f_180_; lean_object* v_synthPendingDepth_181_; lean_object* v_customCanUnfoldPredicate_x3f_182_; uint8_t v_univApprox_183_; uint8_t v_inTypeClassResolution_184_; uint8_t v_cacheInferType_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_207_; 
v_trackZetaDelta_176_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7);
v_zetaDeltaSet_177_ = lean_ctor_get(v___y_171_, 1);
v_lctx_178_ = lean_ctor_get(v___y_171_, 2);
v_localInstances_179_ = lean_ctor_get(v___y_171_, 3);
v_defEqCtx_x3f_180_ = lean_ctor_get(v___y_171_, 4);
v_synthPendingDepth_181_ = lean_ctor_get(v___y_171_, 5);
v_customCanUnfoldPredicate_x3f_182_ = lean_ctor_get(v___y_171_, 6);
v_univApprox_183_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_184_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 2);
v_cacheInferType_185_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 3);
v_isSharedCheck_207_ = !lean_is_exclusive(v___y_171_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v___y_171_, 0);
lean_dec(v_unused_208_);
v___x_187_ = v___y_171_;
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_182_);
lean_inc(v_synthPendingDepth_181_);
lean_inc(v_defEqCtx_x3f_180_);
lean_inc(v_localInstances_179_);
lean_inc(v_lctx_178_);
lean_inc(v_zetaDeltaSet_177_);
lean_dec(v___y_171_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
uint64_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_167_);
v___x_190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_190_, 0, v___x_167_);
lean_ctor_set_uint64(v___x_190_, sizeof(void*)*1, v___x_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_zetaDeltaSet_177_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_lctx_178_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_localInstances_179_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_defEqCtx_x3f_180_);
lean_ctor_set(v_reuseFailAlloc_206_, 5, v_synthPendingDepth_181_);
lean_ctor_set(v_reuseFailAlloc_206_, 6, v_customCanUnfoldPredicate_x3f_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*7, v_trackZetaDelta_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*7 + 1, v_univApprox_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*7 + 2, v_inTypeClassResolution_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*7 + 3, v_cacheInferType_185_);
v___x_192_ = v_reuseFailAlloc_206_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_168_, v_e_169_, v___x_192_, v___y_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_197_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_fst_195_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_fst_195_);
v_snd_196_ = lean_ctor_get(v_a_194_, 1);
lean_inc(v_snd_196_);
lean_dec(v_a_194_);
v___x_197_ = lean_apply_7(v_mkDefeqError_170_, v_fst_195_, v_snd_196_, v___x_192_, v___y_172_, v___y_173_, v___y_174_, lean_box(0));
return v___x_197_;
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v___x_192_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v_mkDefeqError_170_);
v_a_198_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_193_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_193_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__1___boxed(lean_object* v___x_209_, lean_object* v_a_210_, lean_object* v_e_211_, lean_object* v_mkDefeqError_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Elab_Tactic_elabChange___lam__1(v___x_209_, v_a_210_, v_e_211_, v_mkDefeqError_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(lean_object* v_msgData_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v_env_226_; uint8_t v___x_227_; lean_object* v_env_228_; lean_object* v___x_229_; lean_object* v_toCold_230_; lean_object* v_mctx_231_; lean_object* v_lctx_232_; lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_225_ = lean_st_ref_get(v___y_223_);
v_env_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_226_);
lean_dec(v___x_225_);
v___x_227_ = 0;
v_env_228_ = l_Lean_Environment_setRecordingDeps(v_env_226_, v___x_227_);
v___x_229_ = lean_st_ref_get(v___y_221_);
v_toCold_230_ = lean_ctor_get(v___y_222_, 0);
v_mctx_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_mctx_231_);
lean_dec(v___x_229_);
v_lctx_232_ = lean_ctor_get(v___y_220_, 2);
v_options_233_ = lean_ctor_get(v_toCold_230_, 2);
lean_inc_ref(v_options_233_);
lean_inc_ref(v_lctx_232_);
v___x_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_234_, 0, v_env_228_);
lean_ctor_set(v___x_234_, 1, v_mctx_231_);
lean_ctor_set(v___x_234_, 2, v_lctx_232_);
lean_ctor_set(v___x_234_, 3, v_options_233_);
v___x_235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_msgData_219_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0___boxed(lean_object* v_msgData_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msgData_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_ref_250_ = lean_ctor_get(v___y_247_, 2);
v___x_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
lean_inc(v_ref_250_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_ref_250_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg___boxed(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange(lean_object* v_e_268_, lean_object* v_p_269_, lean_object* v_mkDefeqError_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___y_281_; lean_object* v___f_290_; uint8_t v___x_291_; lean_object* v___x_292_; 
lean_inc_ref(v_e_268_);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___lam__0___boxed), 9, 2);
lean_closure_set(v___f_290_, 0, v_e_268_);
lean_closure_set(v___f_290_, 1, v_p_269_);
v___x_291_ = 0;
v___x_292_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___f_290_, v___x_291_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; uint8_t v_foApprox_295_; uint8_t v_ctxApprox_296_; uint8_t v_quasiPatternApprox_297_; uint8_t v_constApprox_298_; uint8_t v_isDefEqStuckEx_299_; uint8_t v_unificationHints_300_; uint8_t v_proofIrrelevance_301_; uint8_t v_offsetCnstrs_302_; uint8_t v_transparency_303_; uint8_t v_etaStruct_304_; uint8_t v_univApprox_305_; uint8_t v_iota_306_; uint8_t v_beta_307_; uint8_t v_proj_308_; uint8_t v_zeta_309_; uint8_t v_zetaDelta_310_; uint8_t v_zetaUnused_311_; uint8_t v_zetaHave_312_; uint8_t v_canUnfoldPredicateConfig_313_; uint8_t v_stringLitToCtor_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_363_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Meta_Context_config(v_a_275_);
v_foApprox_295_ = lean_ctor_get_uint8(v___x_294_, 0);
v_ctxApprox_296_ = lean_ctor_get_uint8(v___x_294_, 1);
v_quasiPatternApprox_297_ = lean_ctor_get_uint8(v___x_294_, 2);
v_constApprox_298_ = lean_ctor_get_uint8(v___x_294_, 3);
v_isDefEqStuckEx_299_ = lean_ctor_get_uint8(v___x_294_, 4);
v_unificationHints_300_ = lean_ctor_get_uint8(v___x_294_, 5);
v_proofIrrelevance_301_ = lean_ctor_get_uint8(v___x_294_, 6);
v_offsetCnstrs_302_ = lean_ctor_get_uint8(v___x_294_, 8);
v_transparency_303_ = lean_ctor_get_uint8(v___x_294_, 9);
v_etaStruct_304_ = lean_ctor_get_uint8(v___x_294_, 10);
v_univApprox_305_ = lean_ctor_get_uint8(v___x_294_, 11);
v_iota_306_ = lean_ctor_get_uint8(v___x_294_, 12);
v_beta_307_ = lean_ctor_get_uint8(v___x_294_, 13);
v_proj_308_ = lean_ctor_get_uint8(v___x_294_, 14);
v_zeta_309_ = lean_ctor_get_uint8(v___x_294_, 15);
v_zetaDelta_310_ = lean_ctor_get_uint8(v___x_294_, 16);
v_zetaUnused_311_ = lean_ctor_get_uint8(v___x_294_, 17);
v_zetaHave_312_ = lean_ctor_get_uint8(v___x_294_, 18);
v_canUnfoldPredicateConfig_313_ = lean_ctor_get_uint8(v___x_294_, 19);
v_stringLitToCtor_314_ = lean_ctor_get_uint8(v___x_294_, 20);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_363_ == 0)
{
v___x_316_ = v___x_294_;
v_isShared_317_ = v_isSharedCheck_363_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___x_294_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_363_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint8_t v_trackZetaDelta_318_; lean_object* v_zetaDeltaSet_319_; lean_object* v_lctx_320_; lean_object* v_localInstances_321_; lean_object* v_defEqCtx_x3f_322_; lean_object* v_synthPendingDepth_323_; lean_object* v_customCanUnfoldPredicate_x3f_324_; uint8_t v_univApprox_325_; uint8_t v_inTypeClassResolution_326_; uint8_t v_cacheInferType_327_; uint8_t v___x_328_; lean_object* v___x_330_; 
v_trackZetaDelta_318_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*7);
v_zetaDeltaSet_319_ = lean_ctor_get(v_a_275_, 1);
v_lctx_320_ = lean_ctor_get(v_a_275_, 2);
v_localInstances_321_ = lean_ctor_get(v_a_275_, 3);
v_defEqCtx_x3f_322_ = lean_ctor_get(v_a_275_, 4);
v_synthPendingDepth_323_ = lean_ctor_get(v_a_275_, 5);
v_customCanUnfoldPredicate_x3f_324_ = lean_ctor_get(v_a_275_, 6);
v_univApprox_325_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_326_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*7 + 2);
v_cacheInferType_327_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*7 + 3);
v___x_328_ = 1;
if (v_isShared_317_ == 0)
{
v___x_330_ = v___x_316_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 0, v_foApprox_295_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 1, v_ctxApprox_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 2, v_quasiPatternApprox_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 3, v_constApprox_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 4, v_isDefEqStuckEx_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 5, v_unificationHints_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 6, v_proofIrrelevance_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 8, v_offsetCnstrs_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 9, v_transparency_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 10, v_etaStruct_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 11, v_univApprox_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 12, v_iota_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 13, v_beta_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 14, v_proj_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 15, v_zeta_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 16, v_zetaDelta_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 17, v_zetaUnused_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 18, v_zetaHave_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 19, v_canUnfoldPredicateConfig_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 20, v_stringLitToCtor_314_);
v___x_330_ = v_reuseFailAlloc_362_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
uint64_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_ctor_set_uint8(v___x_330_, 7, v___x_328_);
v___x_331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set_uint64(v___x_332_, sizeof(void*)*1, v___x_331_);
lean_inc(v_customCanUnfoldPredicate_x3f_324_);
lean_inc(v_synthPendingDepth_323_);
lean_inc(v_defEqCtx_x3f_322_);
lean_inc_ref(v_localInstances_321_);
lean_inc_ref(v_lctx_320_);
lean_inc(v_zetaDeltaSet_319_);
v___x_333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_zetaDeltaSet_319_);
lean_ctor_set(v___x_333_, 2, v_lctx_320_);
lean_ctor_set(v___x_333_, 3, v_localInstances_321_);
lean_ctor_set(v___x_333_, 4, v_defEqCtx_x3f_322_);
lean_ctor_set(v___x_333_, 5, v_synthPendingDepth_323_);
lean_ctor_set(v___x_333_, 6, v_customCanUnfoldPredicate_x3f_324_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*7, v_trackZetaDelta_318_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*7 + 1, v_univApprox_325_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*7 + 2, v_inTypeClassResolution_326_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*7 + 3, v_cacheInferType_327_);
lean_inc_ref(v_e_268_);
lean_inc(v_a_293_);
v___x_334_ = l_Lean_Meta_isExprDefEq(v_a_293_, v_e_268_, v___x_333_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; uint8_t v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = lean_unbox(v_a_335_);
lean_dec(v_a_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v___x_337_ = l_Lean_Meta_Context_config(v___x_333_);
lean_inc_ref(v_e_268_);
lean_inc(v_a_293_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___lam__1___boxed), 9, 4);
lean_closure_set(v___f_338_, 0, v___x_337_);
lean_closure_set(v___f_338_, 1, v_a_293_);
lean_closure_set(v___f_338_, 2, v_e_268_);
lean_closure_set(v___f_338_, 3, v_mkDefeqError_270_);
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_mk_empty_array_with_capacity(v___x_339_);
v___x_341_ = lean_array_push(v___x_340_, v_a_293_);
v___x_342_ = lean_array_push(v___x_341_, v_e_268_);
v___x_343_ = l_Lean_MessageData_ofLazyM(v___f_338_, v___x_342_);
v___x_344_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v___x_343_, v___x_333_, v_a_276_, v_a_277_, v_a_278_);
lean_dec_ref_known(v___x_333_, 7);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v___x_353_; 
lean_dec_ref_known(v___x_333_, 7);
lean_dec_ref(v_mkDefeqError_270_);
lean_dec_ref(v_e_268_);
v___x_353_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_a_293_, v_a_276_);
v___y_281_ = v___x_353_;
goto v___jp_280_;
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref_known(v___x_333_, 7);
lean_dec(v_a_293_);
lean_dec_ref(v_mkDefeqError_270_);
lean_dec_ref(v_e_268_);
v_a_354_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_334_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_334_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_mkDefeqError_270_);
lean_dec_ref(v_e_268_);
return v___x_292_;
}
v___jp_280_:
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___y_281_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___y_281_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___y_281_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___y_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___boxed(lean_object* v_e_364_, lean_object* v_p_365_, lean_object* v_mkDefeqError_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Elab_Tactic_elabChange(v_e_364_, v_p_365_, v_mkDefeqError_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v_msg_378_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___boxed(lean_object* v_00_u03b1_389_, lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(v_00_u03b1_389_, v_msg_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_400_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_box(0);
v___x_402_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg(){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___boxed(lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(lean_object* v_00_u03b1_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___boxed(lean_object* v_00_u03b1_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(v_00_u03b1_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_430_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__0___closed__0));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__0(lean_object* v_x_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_Elab_Tactic_evalChange___lam__0___closed__1, &l_Lean_Elab_Tactic_evalChange___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1);
v___x_445_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v___x_444_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__0___boxed(lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_Tactic_evalChange___lam__0(v_x_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v_x_446_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1(lean_object* v_h_457_, lean_object* v_fst_458_, uint8_t v___x_459_, lean_object* v_snd_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_462_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l_Lean_MVarId_changeLocalDecl(v_a_471_, v_h_457_, v_fst_458_, v___x_459_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_a_473_);
lean_ctor_set(v___x_474_, 1, v_snd_460_);
v___x_475_ = lean_box(0);
v___x_476_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_474_, v___y_462_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_476_, 0);
lean_dec(v_unused_484_);
v___x_478_ = v___x_476_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_dec(v___x_476_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_475_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_475_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
return v___x_476_;
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_snd_460_);
v_a_485_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_472_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_472_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_snd_460_);
lean_dec_ref(v_fst_458_);
lean_dec(v_h_457_);
v_a_493_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_470_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_470_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1___boxed(lean_object* v_h_501_, lean_object* v_fst_502_, lean_object* v___x_503_, lean_object* v_snd_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_2741__boxed_514_; lean_object* v_res_515_; 
v___x_2741__boxed_514_ = lean_unbox(v___x_503_);
v_res_515_ = l_Lean_Elab_Tactic_evalChange___lam__1(v_h_501_, v_fst_502_, v___x_2741__boxed_514_, v_snd_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2(lean_object* v_newType_517_, lean_object* v___x_518_, uint8_t v___x_519_, lean_object* v_h_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
lean_inc(v_h_520_);
v___x_530_ = l_Lean_FVarId_getType___redArg(v_h_520_, v___y_525_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l_Lean_Elab_Tactic_getMainTag___redArg(v___y_522_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__2___closed__0));
v___x_535_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___boxed), 12, 3);
lean_closure_set(v___x_535_, 0, v_a_531_);
lean_closure_set(v___x_535_, 1, v_newType_517_);
lean_closure_set(v___x_535_, 2, v___x_534_);
v___x_536_ = l_Lean_Name_mkStr1(v___x_518_);
v___x_537_ = 0;
v___x_538_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_535_, v_a_533_, v___x_536_, v___x_537_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v_fst_540_ = lean_ctor_get(v_a_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v_a_539_, 1);
lean_inc(v_snd_541_);
lean_dec(v_a_539_);
v___x_542_ = lean_box(v___x_519_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__1___boxed), 13, 4);
lean_closure_set(v___f_543_, 0, v_h_520_);
lean_closure_set(v___f_543_, 1, v_fst_540_);
lean_closure_set(v___f_543_, 2, v___x_542_);
lean_closure_set(v___f_543_, 3, v_snd_541_);
v___x_544_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_543_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
return v___x_544_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_h_520_);
v_a_545_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_538_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_538_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_531_);
lean_dec(v_h_520_);
lean_dec_ref(v___x_518_);
lean_dec(v_newType_517_);
v_a_553_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_532_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_532_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_h_520_);
lean_dec_ref(v___x_518_);
lean_dec(v_newType_517_);
v_a_561_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_530_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_530_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___boxed(lean_object* v_newType_569_, lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v_h_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_2843__boxed_582_; lean_object* v_res_583_; 
v___x_2843__boxed_582_ = lean_unbox(v___x_571_);
v_res_583_ = l_Lean_Elab_Tactic_evalChange___lam__2(v_newType_569_, v___x_570_, v___x_2843__boxed_582_, v_h_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3(lean_object* v_fst_584_, lean_object* v_snd_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_MVarId_replaceTargetDefEq(v_a_596_, v_fst_584_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_598_);
lean_ctor_set(v___x_599_, 1, v_snd_585_);
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_599_, v___y_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v___x_601_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_600_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_600_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
return v___x_601_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_snd_585_);
v_a_610_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_597_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_597_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_snd_585_);
lean_dec_ref(v_fst_584_);
v_a_618_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_595_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_595_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3___boxed(lean_object* v_fst_626_, lean_object* v_snd_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_Tactic_evalChange___lam__3(v_fst_626_, v_snd_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4(lean_object* v_newType_638_, lean_object* v___x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_Tactic_getMainTarget(v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l_Lean_Elab_Tactic_getMainTag___redArg(v___y_641_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__2___closed__0));
v___x_654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___boxed), 12, 3);
lean_closure_set(v___x_654_, 0, v_a_650_);
lean_closure_set(v___x_654_, 1, v_newType_638_);
lean_closure_set(v___x_654_, 2, v___x_653_);
v___x_655_ = l_Lean_Name_mkStr1(v___x_639_);
v___x_656_ = 0;
v___x_657_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_654_, v_a_652_, v___x_655_, v___x_656_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v_fst_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_fst_659_);
v_snd_660_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_658_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__3___boxed), 11, 2);
lean_closure_set(v___f_661_, 0, v_fst_659_);
lean_closure_set(v___f_661_, 1, v_snd_660_);
v___x_662_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_661_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
return v___x_662_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_657_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_a_650_);
lean_dec_ref(v___x_639_);
lean_dec(v_newType_638_);
v_a_671_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_651_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_651_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___x_639_);
lean_dec(v_newType_638_);
v_a_679_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_649_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_649_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4___boxed(lean_object* v_newType_687_, lean_object* v___x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Elab_Tactic_evalChange___lam__4(v_newType_687_, v___x_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange(lean_object* v_x_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__3));
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__4));
lean_inc(v_x_715_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_x_715_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_x_715_);
v___x_728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_728_;
}
else
{
lean_object* v___f_729_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___x_745_; lean_object* v_newType_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___f_729_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__5));
v___x_745_ = lean_unsigned_to_nat(1u);
v_newType_746_ = l_Lean_Syntax_getArg(v_x_715_, v___x_745_);
v___x_747_ = lean_box(v___x_727_);
lean_inc(v_newType_746_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__2___boxed), 13, 3);
lean_closure_set(v___f_748_, 0, v_newType_746_);
lean_closure_set(v___f_748_, 1, v___x_725_);
lean_closure_set(v___f_748_, 2, v___x_747_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__4___boxed), 11, 2);
lean_closure_set(v___f_749_, 0, v_newType_746_);
lean_closure_set(v___f_749_, 1, v___x_725_);
v___x_750_ = lean_unsigned_to_nat(2u);
v___x_751_ = l_Lean_Syntax_getArg(v_x_715_, v___x_750_);
lean_dec(v_x_715_);
v___x_752_ = l_Lean_Syntax_isNone(v___x_751_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
lean_inc(v___x_751_);
v___x_753_ = l_Lean_Syntax_matchesNull(v___x_751_, v___x_745_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec(v___x_751_);
lean_dec_ref(v___f_749_);
lean_dec_ref(v___f_748_);
v___x_754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v_loc_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v_loc_756_ = l_Lean_Syntax_getArg(v___x_751_, v___x_755_);
lean_dec(v___x_751_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__7));
lean_inc(v_loc_756_);
v___x_758_ = l_Lean_Syntax_isOfKind(v_loc_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_loc_756_);
lean_dec_ref(v___f_749_);
lean_dec_ref(v___f_748_);
v___x_759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_759_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v_loc_756_);
v___y_731_ = v_a_718_;
v___y_732_ = v___f_748_;
v___y_733_ = v_a_719_;
v___y_734_ = v_a_723_;
v___y_735_ = v_a_720_;
v___y_736_ = v_a_722_;
v___y_737_ = v___f_749_;
v___y_738_ = v_a_717_;
v___y_739_ = v_a_721_;
v___y_740_ = v_a_716_;
v___y_741_ = v___x_760_;
goto v___jp_730_;
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v___x_751_);
v___x_761_ = lean_box(0);
v___y_731_ = v_a_718_;
v___y_732_ = v___f_748_;
v___y_733_ = v_a_719_;
v___y_734_ = v_a_723_;
v___y_735_ = v_a_720_;
v___y_736_ = v_a_722_;
v___y_737_ = v___f_749_;
v___y_738_ = v_a_717_;
v___y_739_ = v_a_721_;
v___y_740_ = v_a_716_;
v___y_741_ = v___x_761_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_mkOptionalNode(v___y_741_);
v___x_743_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_742_);
lean_dec(v___x_742_);
v___x_744_ = l_Lean_Elab_Tactic_withLocation(v___x_743_, v___y_732_, v___y_737_, v___f_729_, v___y_740_, v___y_738_, v___y_731_, v___y_733_, v___y_735_, v___y_739_, v___y_736_, v___y_734_);
lean_dec(v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___boxed(lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Elab_Tactic_evalChange(v_x_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1(){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__4));
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2));
v___x_784_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___boxed), 10, 0);
v___x_785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_781_, v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2));
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0));
v___x_792_ = l_Lean_addBuiltinDocString(v___x_790_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___boxed(lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
return v_res_794_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Change(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Change(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Change(builtin);
}
#ifdef __cplusplus
}
#endif
