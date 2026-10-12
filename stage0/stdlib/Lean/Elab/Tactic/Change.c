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
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabChangeDefaultError___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(lean_object* v_p_7_, lean_object* v_tgt_8_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_elabChangeDefaultError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_7_ = stack[0].m_obj;
lean_object* v_tgt_8_ = stack[1].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_7_, v_tgt_8_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___boxed(lean_object* v_p_19_, lean_object* v_tgt_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_19_, v_tgt_20_);
return v_res_22_;
}
}
lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError(lean_object* v_p_23_, lean_object* v_tgt_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_23_, v_tgt_24_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabChangeDefaultError_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_23_ = stack[0].m_obj;
lean_object* v_tgt_24_ = stack[1].m_obj;
lean_object* v_a_25_ = stack[2].m_obj;
lean_object* v_a_26_ = stack[3].m_obj;
lean_object* v_a_27_ = stack[4].m_obj;
lean_object* v_a_28_ = stack[5].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Elab_Tactic_elabChangeDefaultError(v_p_23_, v_tgt_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___boxed(lean_object* v_p_32_, lean_object* v_tgt_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Elab_Tactic_elabChangeDefaultError(v_p_32_, v_tgt_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_39_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(lean_object* v_e_40_, lean_object* v___y_41_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = l_Lean_Expr_hasMVar(v_e_40_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_e_40_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v_mctx_46_; lean_object* v___x_47_; lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v___x_50_; lean_object* v_cache_51_; lean_object* v_zetaDeltaFVarIds_52_; lean_object* v_postponed_53_; lean_object* v_diag_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v___x_45_ = lean_st_ref_get(v___y_41_);
v_mctx_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref(v_mctx_46_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_instantiateMVarsCore(v_mctx_46_, v_e_40_);
v_fst_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_fst_48_);
v_snd_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_snd_49_);
lean_dec_ref(v___x_47_);
v___x_50_ = lean_st_ref_take(v___y_41_);
v_cache_51_ = lean_ctor_get(v___x_50_, 1);
v_zetaDeltaFVarIds_52_ = lean_ctor_get(v___x_50_, 2);
v_postponed_53_ = lean_ctor_get(v___x_50_, 3);
v_diag_54_ = lean_ctor_get(v___x_50_, 4);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_64_);
v___x_56_ = v___x_50_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_diag_54_);
lean_inc(v_postponed_53_);
lean_inc(v_zetaDeltaFVarIds_52_);
lean_inc(v_cache_51_);
lean_dec(v___x_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v_snd_49_);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_snd_49_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_cache_51_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_zetaDeltaFVarIds_52_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_postponed_53_);
lean_ctor_set(v_reuseFailAlloc_62_, 4, v_diag_54_);
v___x_59_ = v_reuseFailAlloc_62_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_st_ref_put(v___y_41_, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_fst_48_);
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_40_ = stack[0].m_obj;
lean_object* v___y_41_ = stack[1].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_e_40_, v___y_41_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg___boxed(lean_object* v_e_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_e_66_, v___y_67_);
lean_dec(v___y_67_);
return v_res_69_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(lean_object* v_e_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_e_70_, v___y_76_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_70_ = stack[0].m_obj;
lean_object* v___y_71_ = stack[1].m_obj;
lean_object* v___y_72_ = stack[2].m_obj;
lean_object* v___y_73_ = stack[3].m_obj;
lean_object* v___y_74_ = stack[4].m_obj;
lean_object* v___y_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v___y_77_ = stack[7].m_obj;
lean_object* v___y_78_ = stack[8].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(v_e_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___boxed(lean_object* v_e_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(v_e_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
lean_object* l_Lean_Elab_Tactic_elabChange___lam__0(lean_object* v_e_93_, lean_object* v_p_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
lean_inc_ref(v_e_93_);
v___x_102_ = lean_infer_type(v_e_93_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_160_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_160_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_160_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_160_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 1);
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_159_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = 1;
v___x_110_ = lean_box(0);
v___x_111_ = l_Lean_Elab_Term_elabTermEnsuringType(v_p_94_, v___x_108_, v___x_109_, v___x_109_, v___x_110_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_n(v_a_112_, 2);
lean_dec_ref_known(v___x_111_, 1);
lean_inc_ref(v_e_93_);
v___x_113_ = l_Lean_Meta_isExprDefEq(v_a_112_, v_e_93_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_150_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_150_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_150_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_150_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___x_118_; 
v___x_118_ = lean_unbox(v_a_114_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; 
lean_del_object(v___x_116_);
v___x_119_ = 2;
v___x_120_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
v___x_121_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_119_, v___x_120_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
lean_dec_ref_known(v___x_121_, 1);
lean_inc(v_a_112_);
v___x_122_ = l_Lean_Meta_isExprDefEq(v_a_112_, v_e_93_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_130_);
v___x_124_ = v___x_122_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_dec(v___x_122_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_a_112_);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_112_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_a_112_);
v_a_131_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_122_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_122_);
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
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_112_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_e_93_);
v_a_139_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_121_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_121_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
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
lean_object* v___x_148_; 
lean_dec(v_a_114_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_e_93_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v_a_112_);
v___x_148_ = v___x_116_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_112_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_a_112_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_e_93_);
v_a_151_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_113_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_113_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_e_93_);
return v___x_111_;
}
}
}
}
else
{
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v_p_94_);
lean_dec_ref(v_e_93_);
return v___x_102_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabChange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_93_ = stack[0].m_obj;
lean_object* v_p_94_ = stack[1].m_obj;
lean_object* v___y_95_ = stack[2].m_obj;
lean_object* v___y_96_ = stack[3].m_obj;
lean_object* v___y_97_ = stack[4].m_obj;
lean_object* v___y_98_ = stack[5].m_obj;
lean_object* v___y_99_ = stack[6].m_obj;
lean_object* v___y_100_ = stack[7].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_Elab_Tactic_elabChange___lam__0(v_e_93_, v_p_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0___boxed(lean_object* v_e_162_, lean_object* v_p_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_Tactic_elabChange___lam__0(v_e_162_, v_p_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_171_;
}
}
lean_object* l_Lean_Elab_Tactic_elabChange___lam__1(lean_object* v___x_172_, lean_object* v_a_173_, lean_object* v_e_174_, lean_object* v_mkDefeqError_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
uint8_t v_trackZetaDelta_181_; lean_object* v_zetaDeltaSet_182_; lean_object* v_lctx_183_; lean_object* v_localInstances_184_; lean_object* v_defEqCtx_x3f_185_; lean_object* v_synthPendingDepth_186_; lean_object* v_customCanUnfoldPredicate_x3f_187_; uint8_t v_univApprox_188_; uint8_t v_inTypeClassResolution_189_; uint8_t v_cacheInferType_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_212_; 
v_trackZetaDelta_181_ = lean_ctor_get_uint8(v___y_176_, sizeof(void*)*7);
v_zetaDeltaSet_182_ = lean_ctor_get(v___y_176_, 1);
v_lctx_183_ = lean_ctor_get(v___y_176_, 2);
v_localInstances_184_ = lean_ctor_get(v___y_176_, 3);
v_defEqCtx_x3f_185_ = lean_ctor_get(v___y_176_, 4);
v_synthPendingDepth_186_ = lean_ctor_get(v___y_176_, 5);
v_customCanUnfoldPredicate_x3f_187_ = lean_ctor_get(v___y_176_, 6);
v_univApprox_188_ = lean_ctor_get_uint8(v___y_176_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_189_ = lean_ctor_get_uint8(v___y_176_, sizeof(void*)*7 + 2);
v_cacheInferType_190_ = lean_ctor_get_uint8(v___y_176_, sizeof(void*)*7 + 3);
v_isSharedCheck_212_ = !lean_is_exclusive(v___y_176_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___y_176_, 0);
lean_dec(v_unused_213_);
v___x_192_ = v___y_176_;
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_187_);
lean_inc(v_synthPendingDepth_186_);
lean_inc(v_defEqCtx_x3f_185_);
lean_inc(v_localInstances_184_);
lean_inc(v_lctx_183_);
lean_inc(v_zetaDeltaSet_182_);
lean_dec(v___y_176_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint64_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_172_);
v___x_195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_195_, 0, v___x_172_);
lean_ctor_set_uint64(v___x_195_, sizeof(void*)*1, v___x_194_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_zetaDeltaSet_182_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_lctx_183_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_localInstances_184_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_defEqCtx_x3f_185_);
lean_ctor_set(v_reuseFailAlloc_211_, 5, v_synthPendingDepth_186_);
lean_ctor_set(v_reuseFailAlloc_211_, 6, v_customCanUnfoldPredicate_x3f_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*7, v_trackZetaDelta_181_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*7 + 1, v_univApprox_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*7 + 2, v_inTypeClassResolution_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*7 + 3, v_cacheInferType_190_);
v___x_197_ = v_reuseFailAlloc_211_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_173_, v_e_174_, v___x_197_, v___y_177_, v___y_178_, v___y_179_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_202_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v_fst_200_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_fst_200_);
v_snd_201_ = lean_ctor_get(v_a_199_, 1);
lean_inc(v_snd_201_);
lean_dec(v_a_199_);
v___x_202_ = lean_apply_7(v_mkDefeqError_175_, v_fst_200_, v_snd_201_, v___x_197_, v___y_177_, v___y_178_, v___y_179_, lean_box(0));
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v___x_197_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v_mkDefeqError_175_);
v_a_203_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_198_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_198_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabChange___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_172_ = stack[0].m_obj;
lean_object* v_a_173_ = stack[1].m_obj;
lean_object* v_e_174_ = stack[2].m_obj;
lean_object* v_mkDefeqError_175_ = stack[3].m_obj;
lean_object* v___y_176_ = stack[4].m_obj;
lean_object* v___y_177_ = stack[5].m_obj;
lean_object* v___y_178_ = stack[6].m_obj;
lean_object* v___y_179_ = stack[7].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_Elab_Tactic_elabChange___lam__1(v___x_172_, v_a_173_, v_e_174_, v_mkDefeqError_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__1___boxed(lean_object* v___x_215_, lean_object* v_a_216_, lean_object* v_e_217_, lean_object* v_mkDefeqError_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Tactic_elabChange___lam__1(v___x_215_, v_a_216_, v_e_217_, v_mkDefeqError_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
return v_res_224_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; uint8_t v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_toCold_236_; lean_object* v_mctx_237_; lean_object* v_lctx_238_; lean_object* v_options_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_231_ = lean_st_ref_get(v___y_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = 0;
v_env_234_ = l_Lean_Environment_setRecordingDeps(v_env_232_, v___x_233_);
v___x_235_ = lean_st_ref_get(v___y_227_);
v_toCold_236_ = lean_ctor_get(v___y_228_, 0);
v_mctx_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_mctx_237_);
lean_dec(v___x_235_);
v_lctx_238_ = lean_ctor_get(v___y_226_, 2);
v_options_239_ = lean_ctor_get(v_toCold_236_, 2);
lean_inc_ref(v_options_239_);
lean_inc_ref(v_lctx_238_);
v___x_240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_240_, 0, v_env_234_);
lean_ctor_set(v___x_240_, 1, v_mctx_237_);
lean_ctor_set(v___x_240_, 2, v_lctx_238_);
lean_ctor_set(v___x_240_, 3, v_options_239_);
v___x_241_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_msgData_225_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_225_ = stack[0].m_obj;
lean_object* v___y_226_ = stack[1].m_obj;
lean_object* v___y_227_ = stack[2].m_obj;
lean_object* v___y_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msgData_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0___boxed(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msgData_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_ref_257_; lean_object* v___x_258_; lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_ref_257_ = lean_ctor_get(v___y_254_, 2);
v___x_258_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msg_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_inc(v_ref_257_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_ref_257_);
lean_ctor_set(v___x_263_, 1, v_a_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 1);
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_251_ = stack[0].m_obj;
lean_object* v___y_252_ = stack[1].m_obj;
lean_object* v___y_253_ = stack[2].m_obj;
lean_object* v___y_254_ = stack[3].m_obj;
lean_object* v___y_255_ = stack[4].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v_msg_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg___boxed(lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
lean_object* l_Lean_Elab_Tactic_elabChange(lean_object* v_e_276_, lean_object* v_p_277_, lean_object* v_mkDefeqError_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___y_289_; lean_object* v___f_298_; uint8_t v___x_299_; lean_object* v___x_300_; 
lean_inc_ref(v_e_276_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___lam__0___boxed), 9, 2);
lean_closure_set(v___f_298_, 0, v_e_276_);
lean_closure_set(v___f_298_, 1, v_p_277_);
v___x_299_ = 0;
v___x_300_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___f_298_, v___x_299_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; uint8_t v_foApprox_303_; uint8_t v_ctxApprox_304_; uint8_t v_quasiPatternApprox_305_; uint8_t v_constApprox_306_; uint8_t v_isDefEqStuckEx_307_; uint8_t v_unificationHints_308_; uint8_t v_proofIrrelevance_309_; uint8_t v_offsetCnstrs_310_; uint8_t v_transparency_311_; uint8_t v_etaStruct_312_; uint8_t v_univApprox_313_; uint8_t v_iota_314_; uint8_t v_beta_315_; uint8_t v_proj_316_; uint8_t v_zeta_317_; uint8_t v_zetaDelta_318_; uint8_t v_zetaUnused_319_; uint8_t v_zetaHave_320_; uint8_t v_canUnfoldPredicateConfig_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_370_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Meta_Context_config(v_a_283_);
v_foApprox_303_ = lean_ctor_get_uint8(v___x_302_, 0);
v_ctxApprox_304_ = lean_ctor_get_uint8(v___x_302_, 1);
v_quasiPatternApprox_305_ = lean_ctor_get_uint8(v___x_302_, 2);
v_constApprox_306_ = lean_ctor_get_uint8(v___x_302_, 3);
v_isDefEqStuckEx_307_ = lean_ctor_get_uint8(v___x_302_, 4);
v_unificationHints_308_ = lean_ctor_get_uint8(v___x_302_, 5);
v_proofIrrelevance_309_ = lean_ctor_get_uint8(v___x_302_, 6);
v_offsetCnstrs_310_ = lean_ctor_get_uint8(v___x_302_, 8);
v_transparency_311_ = lean_ctor_get_uint8(v___x_302_, 9);
v_etaStruct_312_ = lean_ctor_get_uint8(v___x_302_, 10);
v_univApprox_313_ = lean_ctor_get_uint8(v___x_302_, 11);
v_iota_314_ = lean_ctor_get_uint8(v___x_302_, 12);
v_beta_315_ = lean_ctor_get_uint8(v___x_302_, 13);
v_proj_316_ = lean_ctor_get_uint8(v___x_302_, 14);
v_zeta_317_ = lean_ctor_get_uint8(v___x_302_, 15);
v_zetaDelta_318_ = lean_ctor_get_uint8(v___x_302_, 16);
v_zetaUnused_319_ = lean_ctor_get_uint8(v___x_302_, 17);
v_zetaHave_320_ = lean_ctor_get_uint8(v___x_302_, 18);
v_canUnfoldPredicateConfig_321_ = lean_ctor_get_uint8(v___x_302_, 19);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_370_ == 0)
{
v___x_323_ = v___x_302_;
v_isShared_324_ = v_isSharedCheck_370_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_302_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_370_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v_trackZetaDelta_325_; lean_object* v_zetaDeltaSet_326_; lean_object* v_lctx_327_; lean_object* v_localInstances_328_; lean_object* v_defEqCtx_x3f_329_; lean_object* v_synthPendingDepth_330_; lean_object* v_customCanUnfoldPredicate_x3f_331_; uint8_t v_univApprox_332_; uint8_t v_inTypeClassResolution_333_; uint8_t v_cacheInferType_334_; uint8_t v___x_335_; lean_object* v___x_337_; 
v_trackZetaDelta_325_ = lean_ctor_get_uint8(v_a_283_, sizeof(void*)*7);
v_zetaDeltaSet_326_ = lean_ctor_get(v_a_283_, 1);
v_lctx_327_ = lean_ctor_get(v_a_283_, 2);
v_localInstances_328_ = lean_ctor_get(v_a_283_, 3);
v_defEqCtx_x3f_329_ = lean_ctor_get(v_a_283_, 4);
v_synthPendingDepth_330_ = lean_ctor_get(v_a_283_, 5);
v_customCanUnfoldPredicate_x3f_331_ = lean_ctor_get(v_a_283_, 6);
v_univApprox_332_ = lean_ctor_get_uint8(v_a_283_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_333_ = lean_ctor_get_uint8(v_a_283_, sizeof(void*)*7 + 2);
v_cacheInferType_334_ = lean_ctor_get_uint8(v_a_283_, sizeof(void*)*7 + 3);
v___x_335_ = 1;
if (v_isShared_324_ == 0)
{
v___x_337_ = v___x_323_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 0, v_foApprox_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 1, v_ctxApprox_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 2, v_quasiPatternApprox_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 3, v_constApprox_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 4, v_isDefEqStuckEx_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 5, v_unificationHints_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 6, v_proofIrrelevance_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 8, v_offsetCnstrs_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 9, v_transparency_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 10, v_etaStruct_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 11, v_univApprox_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 12, v_iota_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 13, v_beta_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 14, v_proj_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 15, v_zeta_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 16, v_zetaDelta_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 17, v_zetaUnused_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 18, v_zetaHave_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, 19, v_canUnfoldPredicateConfig_321_);
v___x_337_ = v_reuseFailAlloc_369_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
uint64_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_ctor_set_uint8(v___x_337_, 7, v___x_335_);
v___x_338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set_uint64(v___x_339_, sizeof(void*)*1, v___x_338_);
lean_inc(v_customCanUnfoldPredicate_x3f_331_);
lean_inc(v_synthPendingDepth_330_);
lean_inc(v_defEqCtx_x3f_329_);
lean_inc_ref(v_localInstances_328_);
lean_inc_ref(v_lctx_327_);
lean_inc(v_zetaDeltaSet_326_);
v___x_340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_zetaDeltaSet_326_);
lean_ctor_set(v___x_340_, 2, v_lctx_327_);
lean_ctor_set(v___x_340_, 3, v_localInstances_328_);
lean_ctor_set(v___x_340_, 4, v_defEqCtx_x3f_329_);
lean_ctor_set(v___x_340_, 5, v_synthPendingDepth_330_);
lean_ctor_set(v___x_340_, 6, v_customCanUnfoldPredicate_x3f_331_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7, v_trackZetaDelta_325_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 1, v_univApprox_332_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 2, v_inTypeClassResolution_333_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 3, v_cacheInferType_334_);
lean_inc_ref(v_e_276_);
lean_inc(v_a_301_);
v___x_341_ = l_Lean_Meta_isExprDefEq(v_a_301_, v_e_276_, v___x_340_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; uint8_t v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = lean_unbox(v_a_342_);
lean_dec(v_a_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v___x_344_ = l_Lean_Meta_Context_config(v___x_340_);
lean_inc_ref(v_e_276_);
lean_inc(v_a_301_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___lam__1___boxed), 9, 4);
lean_closure_set(v___f_345_, 0, v___x_344_);
lean_closure_set(v___f_345_, 1, v_a_301_);
lean_closure_set(v___f_345_, 2, v_e_276_);
lean_closure_set(v___f_345_, 3, v_mkDefeqError_278_);
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_array_push(v___x_347_, v_a_301_);
v___x_349_ = lean_array_push(v___x_348_, v_e_276_);
v___x_350_ = l_Lean_MessageData_ofLazyM(v___f_345_, v___x_349_);
v___x_351_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v___x_350_, v___x_340_, v_a_284_, v_a_285_, v_a_286_);
lean_dec_ref_known(v___x_340_, 7);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v___x_360_; 
lean_dec_ref_known(v___x_340_, 7);
lean_dec_ref(v_mkDefeqError_278_);
lean_dec_ref(v_e_276_);
v___x_360_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_a_301_, v_a_284_);
v___y_289_ = v___x_360_;
goto v___jp_288_;
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref_known(v___x_340_, 7);
lean_dec(v_a_301_);
lean_dec_ref(v_mkDefeqError_278_);
lean_dec_ref(v_e_276_);
v_a_361_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_341_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_341_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_mkDefeqError_278_);
lean_dec_ref(v_e_276_);
return v___x_300_;
}
v___jp_288_:
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___y_289_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___y_289_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___y_289_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___y_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_276_ = stack[0].m_obj;
lean_object* v_p_277_ = stack[1].m_obj;
lean_object* v_mkDefeqError_278_ = stack[2].m_obj;
lean_object* v_a_279_ = stack[3].m_obj;
lean_object* v_a_280_ = stack[4].m_obj;
lean_object* v_a_281_ = stack[5].m_obj;
lean_object* v_a_282_ = stack[6].m_obj;
lean_object* v_a_283_ = stack[7].m_obj;
lean_object* v_a_284_ = stack[8].m_obj;
lean_object* v_a_285_ = stack[9].m_obj;
lean_object* v_a_286_ = stack[10].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Elab_Tactic_elabChange(v_e_276_, v_p_277_, v_mkDefeqError_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___boxed(lean_object* v_e_372_, lean_object* v_p_373_, lean_object* v_mkDefeqError_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Tactic_elabChange(v_e_372_, v_p_373_, v_mkDefeqError_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_384_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v_msg_386_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_386_ = stack[1].m_obj;
lean_object* v___y_387_ = stack[2].m_obj;
lean_object* v___y_388_ = stack[3].m_obj;
lean_object* v___y_389_ = stack[4].m_obj;
lean_object* v___y_390_ = stack[5].m_obj;
lean_object* v___y_391_ = stack[6].m_obj;
lean_object* v___y_392_ = stack[7].m_obj;
lean_object* v___y_393_ = stack[8].m_obj;
lean_object* v___y_394_ = stack[9].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(lean_box(0), v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___boxed(lean_object* v_00_u03b1_398_, lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(v_00_u03b1_398_, v_msg_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_box(0);
v___x_411_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
return v___x_412_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg(){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_416_;
v_res_416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___boxed(lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v_res_418_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(lean_object* v_00_u03b1_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_420_ = stack[1].m_obj;
lean_object* v___y_421_ = stack[2].m_obj;
lean_object* v___y_422_ = stack[3].m_obj;
lean_object* v___y_423_ = stack[4].m_obj;
lean_object* v___y_424_ = stack[5].m_obj;
lean_object* v___y_425_ = stack[6].m_obj;
lean_object* v___y_426_ = stack[7].m_obj;
lean_object* v___y_427_ = stack[8].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(lean_box(0), v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___boxed(lean_object* v_00_u03b1_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(v_00_u03b1_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__0___closed__0));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange___lam__0(lean_object* v_x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_Elab_Tactic_evalChange___lam__0___closed__1, &l_Lean_Elab_Tactic_evalChange___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1);
v___x_456_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(v___x_455_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_445_ = stack[0].m_obj;
lean_object* v___y_446_ = stack[1].m_obj;
lean_object* v___y_447_ = stack[2].m_obj;
lean_object* v___y_448_ = stack[3].m_obj;
lean_object* v___y_449_ = stack[4].m_obj;
lean_object* v___y_450_ = stack[5].m_obj;
lean_object* v___y_451_ = stack[6].m_obj;
lean_object* v___y_452_ = stack[7].m_obj;
lean_object* v___y_453_ = stack[8].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_Elab_Tactic_evalChange___lam__0(v_x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__0___boxed(lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Elab_Tactic_evalChange___lam__0(v_x_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v_x_458_);
return v_res_468_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange___lam__1(lean_object* v_fst_469_, lean_object* v_snd_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_472_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = l_Lean_MVarId_replaceTargetDefEq(v_a_481_, v_fst_469_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v_a_483_);
lean_ctor_set(v___x_484_, 1, v_snd_470_);
v___x_485_ = lean_box(0);
v___x_486_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_484_, v___y_472_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v___x_486_, 0);
lean_dec(v_unused_494_);
v___x_488_ = v___x_486_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_dec(v___x_486_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_485_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_485_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
return v___x_486_;
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_snd_470_);
v_a_495_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_482_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_482_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_snd_470_);
lean_dec_ref(v_fst_469_);
v_a_503_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_480_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_480_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_469_ = stack[0].m_obj;
lean_object* v_snd_470_ = stack[1].m_obj;
lean_object* v___y_471_ = stack[2].m_obj;
lean_object* v___y_472_ = stack[3].m_obj;
lean_object* v___y_473_ = stack[4].m_obj;
lean_object* v___y_474_ = stack[5].m_obj;
lean_object* v___y_475_ = stack[6].m_obj;
lean_object* v___y_476_ = stack[7].m_obj;
lean_object* v___y_477_ = stack[8].m_obj;
lean_object* v___y_478_ = stack[9].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_Elab_Tactic_evalChange___lam__1(v_fst_469_, v_snd_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__1___boxed(lean_object* v_fst_512_, lean_object* v_snd_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Elab_Tactic_evalChange___lam__1(v_fst_512_, v_snd_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_523_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange___lam__2(lean_object* v_newType_525_, lean_object* v___x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Elab_Tactic_getMainTarget(v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = l_Lean_Elab_Tactic_getMainTag___redArg(v___y_528_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__2___closed__0));
v___x_541_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___boxed), 12, 3);
lean_closure_set(v___x_541_, 0, v_a_537_);
lean_closure_set(v___x_541_, 1, v_newType_525_);
lean_closure_set(v___x_541_, 2, v___x_540_);
v___x_542_ = l_Lean_Name_mkStr1(v___x_526_);
v___x_543_ = 0;
v___x_544_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_541_, v_a_539_, v___x_542_, v___x_543_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___f_548_; lean_object* v___x_549_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v_fst_546_ = lean_ctor_get(v_a_545_, 0);
lean_inc(v_fst_546_);
v_snd_547_ = lean_ctor_get(v_a_545_, 1);
lean_inc(v_snd_547_);
lean_dec(v_a_545_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__1___boxed), 11, 2);
lean_closure_set(v___f_548_, 0, v_fst_546_);
lean_closure_set(v___f_548_, 1, v_snd_547_);
v___x_549_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_548_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_549_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_544_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_537_);
lean_dec_ref(v___x_526_);
lean_dec(v_newType_525_);
v_a_558_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_538_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_538_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v___x_526_);
lean_dec(v_newType_525_);
v_a_566_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_536_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_536_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_newType_525_ = stack[0].m_obj;
lean_object* v___x_526_ = stack[1].m_obj;
lean_object* v___y_527_ = stack[2].m_obj;
lean_object* v___y_528_ = stack[3].m_obj;
lean_object* v___y_529_ = stack[4].m_obj;
lean_object* v___y_530_ = stack[5].m_obj;
lean_object* v___y_531_ = stack[6].m_obj;
lean_object* v___y_532_ = stack[7].m_obj;
lean_object* v___y_533_ = stack[8].m_obj;
lean_object* v___y_534_ = stack[9].m_obj;
lean_object* v_res_574_;
v_res_574_ = l_Lean_Elab_Tactic_evalChange___lam__2(v_newType_525_, v___x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__2___boxed(lean_object* v_newType_575_, lean_object* v___x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Elab_Tactic_evalChange___lam__2(v_newType_575_, v___x_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_586_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange___lam__3(lean_object* v_h_587_, lean_object* v_fst_588_, uint8_t v___x_589_, lean_object* v_snd_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_592_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = l_Lean_MVarId_changeLocalDecl(v_a_601_, v_h_587_, v_fst_588_, v___x_589_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_603_);
lean_ctor_set(v___x_604_, 1, v_snd_590_);
v___x_605_ = lean_box(0);
v___x_606_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_604_, v___y_592_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_614_);
v___x_608_ = v___x_606_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_dec(v___x_606_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_605_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_605_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
return v___x_606_;
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_snd_590_);
v_a_615_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_602_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_602_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_snd_590_);
lean_dec_ref(v_fst_588_);
lean_dec(v_h_587_);
v_a_623_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_600_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_600_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_587_ = stack[0].m_obj;
lean_object* v_fst_588_ = stack[1].m_obj;
uint8_t v___x_589_ = stack[2].m_num;
lean_object* v_snd_590_ = stack[3].m_obj;
lean_object* v___y_591_ = stack[4].m_obj;
lean_object* v___y_592_ = stack[5].m_obj;
lean_object* v___y_593_ = stack[6].m_obj;
lean_object* v___y_594_ = stack[7].m_obj;
lean_object* v___y_595_ = stack[8].m_obj;
lean_object* v___y_596_ = stack[9].m_obj;
lean_object* v___y_597_ = stack[10].m_obj;
lean_object* v___y_598_ = stack[11].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_Elab_Tactic_evalChange___lam__3(v_h_587_, v_fst_588_, v___x_589_, v_snd_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__3___boxed(lean_object* v_h_632_, lean_object* v_fst_633_, lean_object* v___x_634_, lean_object* v_snd_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v___x_3112__boxed_645_; lean_object* v_res_646_; 
v___x_3112__boxed_645_ = lean_unbox(v___x_634_);
v_res_646_ = l_Lean_Elab_Tactic_evalChange___lam__3(v_h_632_, v_fst_633_, v___x_3112__boxed_645_, v_snd_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_646_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange___lam__4(lean_object* v_newType_647_, lean_object* v___x_648_, uint8_t v___x_649_, lean_object* v_h_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
lean_inc(v_h_650_);
v___x_660_ = l_Lean_FVarId_getType___redArg(v_h_650_, v___y_655_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = l_Lean_Elab_Tactic_getMainTag___redArg(v___y_652_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___lam__2___closed__0));
v___x_665_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___boxed), 12, 3);
lean_closure_set(v___x_665_, 0, v_a_661_);
lean_closure_set(v___x_665_, 1, v_newType_647_);
lean_closure_set(v___x_665_, 2, v___x_664_);
v___x_666_ = l_Lean_Name_mkStr1(v___x_648_);
v___x_667_ = 0;
v___x_668_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_665_, v_a_663_, v___x_666_, v___x_667_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_674_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v_fst_670_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_fst_670_);
v_snd_671_ = lean_ctor_get(v_a_669_, 1);
lean_inc(v_snd_671_);
lean_dec(v_a_669_);
v___x_672_ = lean_box(v___x_649_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__3___boxed), 13, 4);
lean_closure_set(v___f_673_, 0, v_h_650_);
lean_closure_set(v___f_673_, 1, v_fst_670_);
lean_closure_set(v___f_673_, 2, v___x_672_);
lean_closure_set(v___f_673_, 3, v_snd_671_);
v___x_674_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_673_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_674_;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_h_650_);
v_a_675_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_668_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_668_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_661_);
lean_dec(v_h_650_);
lean_dec_ref(v___x_648_);
lean_dec(v_newType_647_);
v_a_683_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_662_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_662_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_h_650_);
lean_dec_ref(v___x_648_);
lean_dec(v_newType_647_);
v_a_691_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_660_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_660_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_newType_647_ = stack[0].m_obj;
lean_object* v___x_648_ = stack[1].m_obj;
uint8_t v___x_649_ = stack[2].m_num;
lean_object* v_h_650_ = stack[3].m_obj;
lean_object* v___y_651_ = stack[4].m_obj;
lean_object* v___y_652_ = stack[5].m_obj;
lean_object* v___y_653_ = stack[6].m_obj;
lean_object* v___y_654_ = stack[7].m_obj;
lean_object* v___y_655_ = stack[8].m_obj;
lean_object* v___y_656_ = stack[9].m_obj;
lean_object* v___y_657_ = stack[10].m_obj;
lean_object* v___y_658_ = stack[11].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_Elab_Tactic_evalChange___lam__4(v_newType_647_, v___x_648_, v___x_649_, v_h_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___lam__4___boxed(lean_object* v_newType_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v_h_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_3268__boxed_713_; lean_object* v_res_714_; 
v___x_3268__boxed_713_ = lean_unbox(v___x_702_);
v_res_714_ = l_Lean_Elab_Tactic_evalChange___lam__4(v_newType_700_, v___x_701_, v___x_3268__boxed_713_, v_h_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_714_;
}
}
lean_object* l_Lean_Elab_Tactic_evalChange(lean_object* v_x_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__3));
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__4));
lean_inc(v_x_731_);
v___x_743_ = l_Lean_Syntax_isOfKind(v_x_731_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_x_731_);
v___x_744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_744_;
}
else
{
lean_object* v___f_745_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___x_761_; lean_object* v_newType_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___f_765_; lean_object* v_val_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___f_745_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__5));
v___x_761_ = lean_unsigned_to_nat(1u);
v_newType_762_ = l_Lean_Syntax_getArg(v_x_731_, v___x_761_);
lean_inc(v_newType_762_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__2___boxed), 11, 2);
lean_closure_set(v___f_763_, 0, v_newType_762_);
lean_closure_set(v___f_763_, 1, v___x_741_);
v___x_764_ = lean_box(v___x_743_);
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___lam__4___boxed), 13, 3);
lean_closure_set(v___f_765_, 0, v_newType_762_);
lean_closure_set(v___f_765_, 1, v___x_741_);
lean_closure_set(v___f_765_, 2, v___x_764_);
v___x_777_ = lean_unsigned_to_nat(2u);
v___x_778_ = l_Lean_Syntax_getArg(v_x_731_, v___x_777_);
lean_dec(v_x_731_);
v___x_779_ = l_Lean_Syntax_isNone(v___x_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
lean_inc(v___x_778_);
v___x_780_ = l_Lean_Syntax_matchesNull(v___x_778_, v___x_761_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v___x_778_);
lean_dec_ref(v___f_765_);
lean_dec_ref(v___f_763_);
v___x_781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v_loc_783_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v_loc_783_ = l_Lean_Syntax_getArg(v___x_778_, v___x_782_);
lean_dec(v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__7));
lean_inc(v_loc_783_);
v___x_785_ = l_Lean_Syntax_isOfKind(v_loc_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v_loc_783_);
lean_dec_ref(v___f_765_);
lean_dec_ref(v___f_763_);
v___x_786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
return v___x_786_;
}
else
{
v_val_767_ = v_loc_783_;
v___y_768_ = v_a_732_;
v___y_769_ = v_a_733_;
v___y_770_ = v_a_734_;
v___y_771_ = v_a_735_;
v___y_772_ = v_a_736_;
v___y_773_ = v_a_737_;
v___y_774_ = v_a_738_;
v___y_775_ = v_a_739_;
goto v___jp_766_;
}
}
else
{
v_val_767_ = v_loc_783_;
v___y_768_ = v_a_732_;
v___y_769_ = v_a_733_;
v___y_770_ = v_a_734_;
v___y_771_ = v_a_735_;
v___y_772_ = v_a_736_;
v___y_773_ = v_a_737_;
v___y_774_ = v_a_738_;
v___y_775_ = v_a_739_;
goto v___jp_766_;
}
}
}
else
{
lean_object* v___x_787_; 
lean_dec(v___x_778_);
v___x_787_ = lean_box(0);
v___y_747_ = v_a_733_;
v___y_748_ = v_a_732_;
v___y_749_ = v_a_736_;
v___y_750_ = v_a_734_;
v___y_751_ = v_a_738_;
v___y_752_ = v_a_739_;
v___y_753_ = v___f_765_;
v___y_754_ = v_a_735_;
v___y_755_ = v___f_763_;
v___y_756_ = v_a_737_;
v___y_757_ = v___x_787_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_mkOptionalNode(v___y_757_);
v___x_759_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_758_);
lean_dec(v___x_758_);
v___x_760_ = l_Lean_Elab_Tactic_withLocation(v___x_759_, v___y_753_, v___y_755_, v___f_745_, v___y_748_, v___y_747_, v___y_750_, v___y_754_, v___y_749_, v___y_756_, v___y_751_, v___y_752_);
lean_dec(v___x_759_);
return v___x_760_;
}
v___jp_766_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_val_767_);
v___y_747_ = v___y_769_;
v___y_748_ = v___y_768_;
v___y_749_ = v___y_772_;
v___y_750_ = v___y_770_;
v___y_751_ = v___y_774_;
v___y_752_ = v___y_775_;
v___y_753_ = v___f_765_;
v___y_754_ = v___y_771_;
v___y_755_ = v___f_763_;
v___y_756_ = v___y_773_;
v___y_757_ = v___x_776_;
goto v___jp_746_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_731_ = stack[0].m_obj;
lean_object* v_a_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_a_734_ = stack[3].m_obj;
lean_object* v_a_735_ = stack[4].m_obj;
lean_object* v_a_736_ = stack[5].m_obj;
lean_object* v_a_737_ = stack[6].m_obj;
lean_object* v_a_738_ = stack[7].m_obj;
lean_object* v_a_739_ = stack[8].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_Elab_Tactic_evalChange(v_x_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalChange___boxed(lean_object* v_x_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Elab_Tactic_evalChange(v_x_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_799_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1(){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_809_ = ((lean_object*)(l_Lean_Elab_Tactic_evalChange___closed__4));
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2));
v___x_811_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChange___boxed), 10, 0);
v___x_812_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_808_, v___x_809_, v___x_810_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_813_;
v_res_813_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___boxed(lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
return v_res_815_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3(){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2));
v___x_819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0));
v___x_820_ = l_Lean_addBuiltinDocString(v___x_818_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_821_;
v_res_821_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___boxed(lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
return v_res_823_;
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
