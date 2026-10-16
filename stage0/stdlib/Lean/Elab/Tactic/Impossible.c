// Lean compiler output
// Module: Lean.Elab.Tactic.Impossible
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Elab.ConfigEval public import Lean.Meta.Tactic.Cleanup public import Lean.Meta.Tactic.Revert public import Lean.Meta.Tactic.Intro public import Lean.Meta.Closure
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_admitGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2;
static const lean_closure_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ImpossibleConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 120, 150, 23, 148, 41, 121, 54)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "levels"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 120, 150, 23, 148, 41, 121, 54)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(14, 254, 80, 38, 246, 227, 14, 53)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__6;
static const lean_array_object l_Lean_Elab_Tactic_evalImpossible___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalImpossible___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_impossible"};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalImpossible___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__8_value),LEAN_SCALAR_PTR_LITERAL(88, 100, 77, 38, 182, 7, 158, 172)}};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_evalImpossible___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`impossible`: goal contains universe metavariables"};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "impossible"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 33, 97, 219, 32, 14, 246, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalImpossible"};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(131, 140, 35, 12, 176, 15, 39, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(lean_object* v_type_19_, lean_object* v_maxFVars_x3f_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_19_, v_maxFVars_x3f_20_, v___f_29_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___boxed(lean_object* v_type_47_, lean_object* v_maxFVars_x3f_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v_type_47_, v_maxFVars_x3f_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_maxFVars_x3f_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, uint8_t v_whnfType_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v_type_61_, v_maxFVars_x3f_62_, v_k_63_, v_cleanupAnnotations_64_, v_whnfType_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_maxFVars_x3f_74_, lean_object* v_k_75_, lean_object* v_cleanupAnnotations_76_, lean_object* v_whnfType_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_83_; uint8_t v_whnfType_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_83_ = lean_unbox(v_cleanupAnnotations_76_);
v_whnfType_boxed_84_ = lean_unbox(v_whnfType_77_);
v_res_85_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0(v_00_u03b1_72_, v_type_73_, v_maxFVars_x3f_74_, v_k_75_, v_cleanupAnnotations_boxed_83_, v_whnfType_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(lean_object* v_mvarId_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_102_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_93_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg___boxed(lean_object* v_mvarId_110_, lean_object* v_x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mvarId_110_, v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3(lean_object* v_00_u03b1_118_, lean_object* v_mvarId_119_, lean_object* v_x_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mvarId_119_, v_x_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___boxed(lean_object* v_00_u03b1_127_, lean_object* v_mvarId_128_, lean_object* v_x_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3(v_00_u03b1_127_, v_mvarId_128_, v_x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(uint8_t v___x_139_, lean_object* v___x_140_, lean_object* v_ms_141_, lean_object* v_revBody_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_negBody_149_; lean_object* v___x_153_; 
lean_inc_ref(v_revBody_142_);
v___x_153_ = l_Lean_Meta_isProp(v_revBody_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; uint8_t v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = lean_unbox(v_a_154_);
lean_dec(v_a_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_140_);
v___x_158_ = l_Lean_mkArrow(v_revBody_142_, v___x_157_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v_negBody_149_ = v_a_159_;
goto v___jp_148_;
}
else
{
return v___x_158_;
}
}
else
{
lean_object* v___x_160_; 
lean_dec(v___x_140_);
v___x_160_ = l_Lean_mkNot(v_revBody_142_);
v_negBody_149_ = v___x_160_;
goto v___jp_148_;
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_dec_ref(v_revBody_142_);
lean_dec(v___x_140_);
v_a_161_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_153_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_153_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
v___jp_148_:
{
uint8_t v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; 
v___x_150_ = 1;
v___x_151_ = 1;
v___x_152_ = l_Lean_Meta_mkForallFVars(v_ms_141_, v_negBody_149_, v___x_139_, v___x_150_, v___x_150_, v___x_151_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed(lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v_ms_171_, lean_object* v_revBody_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
uint8_t v___x_3356__boxed_178_; lean_object* v_res_179_; 
v___x_3356__boxed_178_ = lean_unbox(v___x_169_);
v_res_179_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(v___x_3356__boxed_178_, v___x_170_, v_ms_171_, v_revBody_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_ms_171_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(size_t v_sz_180_, size_t v_i_181_, lean_object* v_bs_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_lt(v_i_181_, v_sz_180_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v_bs_182_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v_bs_x27_191_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v_bs_x27_191_ = lean_array_uset(v_bs_182_, v_i_181_, v___x_190_);
v___x_192_ = l_Lean_Meta_mkFreshLevelMVar(v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_181_, v___x_194_);
v___x_196_ = lean_array_uset(v_bs_x27_191_, v_i_181_, v_a_193_);
v_i_181_ = v___x_195_;
v_bs_182_ = v___x_196_;
goto _start;
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_bs_x27_191_);
v_a_198_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_192_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_192_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2___boxed(lean_object* v_sz_206_, lean_object* v_i_207_, lean_object* v_bs_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
size_t v_sz_boxed_214_; size_t v_i_boxed_215_; lean_object* v_res_216_; 
v_sz_boxed_214_ = lean_unbox_usize(v_sz_206_);
lean_dec(v_sz_206_);
v_i_boxed_215_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_boxed_214_, v_i_boxed_215_, v_bs_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(size_t v_sz_220_, size_t v_i_221_, lean_object* v_bs_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_221_, v_sz_220_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_bs_222_);
return v___x_229_;
}
else
{
lean_object* v_v_230_; lean_object* v___x_231_; lean_object* v_bs_x27_232_; lean_object* v_a_234_; 
v_v_230_ = lean_array_uget(v_bs_222_, v_i_221_);
v___x_231_ = lean_unsigned_to_nat(0u);
v_bs_x27_232_ = lean_array_uset(v_bs_222_, v_i_221_, v___x_231_);
if (lean_obj_tag(v_v_230_) == 2)
{
lean_object* v_mvarId_239_; lean_object* v___x_240_; 
v_mvarId_239_ = lean_ctor_get(v_v_230_, 0);
lean_inc(v_mvarId_239_);
lean_dec_ref_known(v_v_230_, 1);
v___x_240_ = l_Lean_MVarId_getDecl(v_mvarId_239_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v_userName_242_; uint8_t v___x_243_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v_userName_242_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_userName_242_);
lean_dec(v_a_241_);
v___x_243_ = l_Lean_Name_isAnonymous(v_userName_242_);
if (v___x_243_ == 0)
{
v_a_234_ = v_userName_242_;
goto v___jp_233_;
}
else
{
lean_object* v___x_244_; 
lean_dec(v_userName_242_);
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1));
v_a_234_ = v___x_244_;
goto v___jp_233_;
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_bs_x27_232_);
v_a_245_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_240_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_240_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v___x_253_; 
lean_dec(v_v_230_);
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1));
v_a_234_ = v___x_253_;
goto v___jp_233_;
}
v___jp_233_:
{
size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_221_, v___x_235_);
v___x_237_ = lean_array_uset(v_bs_x27_232_, v_i_221_, v_a_234_);
v_i_221_ = v___x_236_;
v_bs_222_ = v___x_237_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___boxed(lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_bs_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_263_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_boxed_262_, v_i_boxed_263_, v_bs_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1));
v___x_270_ = l_Lean_mkConst(v___x_269_, v___x_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(lean_object* v_goalType_275_, lean_object* v___x_276_, uint8_t v_cfg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_275_, v___x_276_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Expr_mvarId_x21(v_a_284_);
lean_dec(v_a_284_);
v___x_286_ = l_Lean_MVarId_revertAll(v___x_285_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_MVarId_getType(v_a_287_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2);
v___x_291_ = 0;
v___f_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3));
v___x_293_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_a_289_, v___x_290_, v___x_291_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_rTypeLevels_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
if (v_cfg_277_ == 0)
{
lean_object* v_levelArgs_337_; 
v_levelArgs_337_ = lean_ctor_get(v_a_294_, 3);
lean_inc_ref(v_levelArgs_337_);
v_rTypeLevels_296_ = v_levelArgs_337_;
v___y_297_ = v___y_278_;
v___y_298_ = v___y_279_;
v___y_299_ = v___y_280_;
v___y_300_ = v___y_281_;
goto v___jp_295_;
}
else
{
lean_object* v_levelParams_338_; size_t v_sz_339_; size_t v___x_340_; lean_object* v___x_341_; 
v_levelParams_338_ = lean_ctor_get(v_a_294_, 0);
v_sz_339_ = lean_array_size(v_levelParams_338_);
v___x_340_ = ((size_t)0ULL);
lean_inc_ref(v_levelParams_338_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_339_, v___x_340_, v_levelParams_338_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v_rTypeLevels_296_ = v_a_342_;
v___y_297_ = v___y_278_;
v___y_298_ = v___y_279_;
v___y_299_ = v___y_280_;
v___y_300_ = v___y_281_;
goto v___jp_295_;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_294_);
v_a_343_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
v___jp_295_:
{
lean_object* v_levelParams_301_; lean_object* v_type_302_; lean_object* v_exprArgs_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_levelParams_301_ = lean_ctor_get(v_a_294_, 0);
lean_inc_ref(v_levelParams_301_);
v_type_302_ = lean_ctor_get(v_a_294_, 1);
lean_inc_ref(v_type_302_);
v_exprArgs_303_ = lean_ctor_get(v_a_294_, 4);
lean_inc_ref(v_exprArgs_303_);
lean_dec(v_a_294_);
v___x_304_ = l_Lean_Expr_instantiateLevelParamsArray(v_type_302_, v_levelParams_301_, v_rTypeLevels_296_);
lean_dec_ref(v_type_302_);
v___x_305_ = lean_array_get_size(v_exprArgs_303_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v___x_304_, v___x_306_, v___f_292_, v___x_291_, v___x_291_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; size_t v_sz_309_; size_t v___x_310_; lean_object* v___x_311_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_sz_309_ = lean_array_size(v_exprArgs_303_);
v___x_310_ = ((size_t)0ULL);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_309_, v___x_310_, v_exprArgs_303_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_308_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_a_308_);
v_a_321_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_311_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_311_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_exprArgs_303_);
v_a_329_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_307_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_307_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_293_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_293_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_288_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_288_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_367_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_286_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_286_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_283_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_283_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed(lean_object* v_goalType_383_, lean_object* v___x_384_, lean_object* v_cfg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v_cfg_boxed_391_; lean_object* v_res_392_; 
v_cfg_boxed_391_ = lean_unbox(v_cfg_385_);
v_res_392_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(v_goalType_383_, v___x_384_, v_cfg_boxed_391_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(lean_object* v_mainGoal_393_, lean_object* v_goalType_394_, uint8_t v_cfg_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_box(v_cfg_395_);
v___f_403_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed), 8, 3);
lean_closure_set(v___f_403_, 0, v_goalType_394_);
lean_closure_set(v___f_403_, 1, v___x_401_);
lean_closure_set(v___f_403_, 2, v___x_402_);
v___x_404_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mainGoal_393_, v___f_403_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___boxed(lean_object* v_mainGoal_405_, lean_object* v_goalType_406_, lean_object* v_cfg_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
uint8_t v_cfg_boxed_413_; lean_object* v_res_414_; 
v_cfg_boxed_413_ = lean_unbox(v_cfg_407_);
v_res_414_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(v_mainGoal_405_, v_goalType_406_, v_cfg_boxed_413_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_414_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(lean_object* v_00_u03b1_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(v_00_u03b1_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(lean_object* v_msgData_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; lean_object* v_env_444_; uint8_t v___x_445_; lean_object* v_env_446_; lean_object* v___x_447_; lean_object* v_toCold_448_; lean_object* v_mctx_449_; lean_object* v_lctx_450_; lean_object* v_options_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_443_ = lean_st_ref_get(v___y_441_);
v_env_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_env_444_);
lean_dec(v___x_443_);
v___x_445_ = 0;
v_env_446_ = l_Lean_Environment_setRecordingDeps(v_env_444_, v___x_445_);
v___x_447_ = lean_st_ref_get(v___y_439_);
v_toCold_448_ = lean_ctor_get(v___y_440_, 0);
v_mctx_449_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_mctx_449_);
lean_dec(v___x_447_);
v_lctx_450_ = lean_ctor_get(v___y_438_, 2);
v_options_451_ = lean_ctor_get(v_toCold_448_, 2);
lean_inc_ref(v_options_451_);
lean_inc_ref(v_lctx_450_);
v___x_452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_452_, 0, v_env_446_);
lean_ctor_set(v___x_452_, 1, v_mctx_449_);
lean_ctor_set(v___x_452_, 2, v_lctx_450_);
lean_ctor_set(v___x_452_, 3, v_options_451_);
v___x_453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v_msgData_437_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msgData_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_ref_468_; lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_ref_468_ = lean_ctor_get(v___y_465_, 2);
v___x_469_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_inc(v_ref_468_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_ref_468_);
lean_ctor_set(v___x_474_, 1, v_a_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 1);
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(lean_object* v___x_490_, lean_object* v_ctor_491_, lean_object* v_args_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0));
v___x_519_ = lean_string_dec_eq(v_ctor_491_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_array_get_size(v_args_492_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2);
v___x_525_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v___x_524_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
goto v___jp_498_;
}
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_array_get_borrowed(v___x_490_, v_args_492_, v___x_499_);
lean_inc(v___x_500_);
v___x_501_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_500_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_501_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(lean_object* v___x_534_, lean_object* v_ctor_535_, lean_object* v_args_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(v___x_534_, v_ctor_535_, v_args_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec_ref(v_args_536_);
lean_dec_ref(v_ctor_535_);
lean_dec_ref(v___x_534_);
return v_res_542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v___f_544_; 
v___x_543_ = l_Lean_instInhabitedExpr;
v___f_544_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_544_, 0, v___x_543_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___f_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___f_560_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0);
v___x_561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_562_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_561_, v___f_560_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed(lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(lean_object* v_00_u03b1_570_, lean_object* v_msg_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(v_00_u03b1_578_, v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_589_ = l_Lean_Expr_const___override(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0));
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3);
return v___x_595_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(1);
v___x_597_ = l_Lean_MessageData_ofFormat(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_602_ = l_Lean_MessageData_ofFormat(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
return v_x_603_;
}
else
{
lean_object* v_head_605_; lean_object* v_tail_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_628_; 
v_head_605_ = lean_ctor_get(v_x_604_, 0);
v_tail_606_ = lean_ctor_get(v_x_604_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_628_ == 0)
{
v___x_608_ = v_x_604_;
v_isShared_609_ = v_isSharedCheck_628_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_tail_606_);
lean_inc(v_head_605_);
lean_dec(v_x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_628_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_before_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_626_; 
v_before_610_ = lean_ctor_get(v_head_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_head_605_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_head_605_, 1);
lean_dec(v_unused_627_);
v___x_612_ = v_head_605_;
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_before_610_);
lean_dec(v_head_605_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 7);
lean_ctor_set(v___x_612_, 1, v___x_614_);
lean_ctor_set(v___x_612_, 0, v_x_603_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_x_603_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_625_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 7);
lean_ctor_set(v___x_608_, 1, v___x_617_);
lean_ctor_set(v___x_608_, 0, v___x_616_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_624_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_MessageData_ofSyntax(v_before_610_);
v___x_621_ = l_Lean_indentD(v___x_620_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_619_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v_x_603_ = v___x_622_;
v_x_604_ = v_tail_606_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_629_, lean_object* v_opt_630_){
_start:
{
lean_object* v_name_631_; lean_object* v_defValue_632_; lean_object* v_map_633_; lean_object* v___x_634_; 
v_name_631_ = lean_ctor_get(v_opt_630_, 0);
v_defValue_632_ = lean_ctor_get(v_opt_630_, 1);
v_map_633_ = lean_ctor_get(v_opts_629_, 0);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_633_, v_name_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
uint8_t v___x_635_; 
v___x_635_ = lean_unbox(v_defValue_632_);
return v___x_635_;
}
else
{
lean_object* v_val_636_; 
v_val_636_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_634_, 1);
if (lean_obj_tag(v_val_636_) == 1)
{
uint8_t v_v_637_; 
v_v_637_ = lean_ctor_get_uint8(v_val_636_, 0);
lean_dec_ref_known(v_val_636_, 0);
return v_v_637_;
}
else
{
uint8_t v___x_638_; 
lean_dec(v_val_636_);
v___x_638_ = lean_unbox(v_defValue_632_);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_639_, lean_object* v_opt_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_639_, v_opt_640_);
lean_dec_ref(v_opt_640_);
lean_dec_ref(v_opts_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_647_ = l_Lean_MessageData_ofFormat(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_648_, lean_object* v_macroStack_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_650_);
v___x_653_ = l_Lean_Elab_pp_macroStack;
v___x_654_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_652_, v___x_653_);
lean_dec_ref(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v_macroStack_649_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_msgData_648_);
return v___x_655_;
}
else
{
if (lean_obj_tag(v_macroStack_649_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_msgData_648_);
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v_after_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_673_; 
v_head_657_ = lean_ctor_get(v_macroStack_649_, 0);
lean_inc(v_head_657_);
v_after_658_ = lean_ctor_get(v_head_657_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_head_657_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_head_657_, 0);
lean_dec(v_unused_674_);
v___x_660_ = v_head_657_;
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_after_658_);
lean_dec(v_head_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 7);
lean_ctor_set(v___x_660_, 1, v___x_662_);
lean_ctor_set(v___x_660_, 0, v_msgData_648_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_msgData_648_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_672_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_msgData_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_665_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_MessageData_ofSyntax(v_after_658_);
v___x_668_ = l_Lean_indentD(v___x_667_);
v_msgData_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_669_, 0, v___x_666_);
lean_ctor_set(v_msgData_669_, 1, v___x_668_);
v___x_670_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_669_, v_macroStack_649_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_675_, lean_object* v_macroStack_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_675_, v_macroStack_676_, v___y_677_);
lean_dec_ref(v___y_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_ref_688_; lean_object* v_macroStack_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_ref_688_ = lean_ctor_get(v___y_685_, 2);
v_macroStack_689_ = lean_ctor_get(v___y_681_, 1);
v___x_690_ = l_Lean_Elab_getBetterRef(v_ref_688_, v_macroStack_689_);
v___x_691_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_680_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
lean_inc(v_macroStack_689_);
v___x_693_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_692_, v_macroStack_689_, v___y_685_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_690_);
lean_ctor_set(v___x_698_, 1, v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 1);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
v___x_713_ = l_Lean_Elab_abortTermExceptionId;
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_hasMVar(v_e_720_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v_e_720_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v_mctx_726_; lean_object* v___x_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_730_; lean_object* v_cache_731_; lean_object* v_zetaDeltaFVarIds_732_; lean_object* v_postponed_733_; lean_object* v_diag_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v___x_725_ = lean_st_ref_get(v___y_721_);
v_mctx_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_mctx_726_);
lean_dec(v___x_725_);
v___x_727_ = l_Lean_instantiateMVarsCore(v_mctx_726_, v_e_720_);
v_fst_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_fst_728_);
v_snd_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_snd_729_);
lean_dec_ref(v___x_727_);
v___x_730_ = lean_st_ref_take(v___y_721_);
v_cache_731_ = lean_ctor_get(v___x_730_, 1);
v_zetaDeltaFVarIds_732_ = lean_ctor_get(v___x_730_, 2);
v_postponed_733_ = lean_ctor_get(v___x_730_, 3);
v_diag_734_ = lean_ctor_get(v___x_730_, 4);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_730_, 0);
lean_dec(v_unused_744_);
v___x_736_ = v___x_730_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_diag_734_);
lean_inc(v_postponed_733_);
lean_inc(v_zetaDeltaFVarIds_732_);
lean_inc(v_cache_731_);
lean_dec(v___x_730_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_snd_729_);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_snd_729_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_cache_731_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_zetaDeltaFVarIds_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_postponed_733_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_diag_734_);
v___x_739_ = v_reuseFailAlloc_742_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_st_ref_put(v___y_721_, v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_fst_728_);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_745_, v___y_746_);
lean_dec(v___y_746_);
return v_res_748_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
v___x_753_ = l_Lean_MessageData_ofExpr(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2);
v___x_755_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5);
v___x_761_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(lean_object* v_stx_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_ty_x3f_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_toCold_783_; lean_object* v_currRecDepth_784_; lean_object* v_ref_785_; uint16_t v_optionFlags_786_; uint8_t v_suppressElabErrors_787_; uint8_t v_isRecordingDeps_788_; uint8_t v___x_789_; lean_object* v_ref_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_ty_x3f_777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
v___x_778_ = 1;
v___x_779_ = lean_box(0);
v___x_780_ = lean_box(v___x_778_);
v___x_781_ = lean_box(v___x_778_);
lean_inc(v_stx_769_);
v___x_782_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_782_, 0, v_stx_769_);
lean_closure_set(v___x_782_, 1, v_ty_x3f_777_);
lean_closure_set(v___x_782_, 2, v___x_780_);
lean_closure_set(v___x_782_, 3, v___x_781_);
lean_closure_set(v___x_782_, 4, v___x_779_);
v_toCold_783_ = lean_ctor_get(v_a_774_, 0);
v_currRecDepth_784_ = lean_ctor_get(v_a_774_, 1);
v_ref_785_ = lean_ctor_get(v_a_774_, 2);
v_optionFlags_786_ = lean_ctor_get_uint16(v_a_774_, sizeof(void*)*3);
v_suppressElabErrors_787_ = lean_ctor_get_uint8(v_a_774_, sizeof(void*)*3 + 2);
v_isRecordingDeps_788_ = lean_ctor_get_uint8(v_a_774_, sizeof(void*)*3 + 3);
v___x_789_ = 1;
v_ref_790_ = l_Lean_replaceRef(v_stx_769_, v_ref_785_);
lean_dec(v_stx_769_);
lean_inc(v_currRecDepth_784_);
lean_inc_ref(v_toCold_783_);
v___x_791_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_791_, 0, v_toCold_783_);
lean_ctor_set(v___x_791_, 1, v_currRecDepth_784_);
lean_ctor_set(v___x_791_, 2, v_ref_790_);
lean_ctor_set_uint16(v___x_791_, sizeof(void*)*3, v_optionFlags_786_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3 + 2, v_suppressElabErrors_787_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3 + 3, v_isRecordingDeps_788_);
v___x_792_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_782_, v___x_789_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v___x_791_, v_a_775_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; uint8_t v___x_879_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_793_, v_a_773_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_879_ = l_Lean_Expr_hasSorry(v_a_795_);
if (v___x_879_ == 0)
{
v___y_824_ = v_a_770_;
v___y_825_ = v_a_771_;
v___y_826_ = v_a_772_;
v___y_827_ = v_a_773_;
v___y_828_ = v___x_791_;
v___y_829_ = v_a_775_;
goto v___jp_823_;
}
else
{
uint8_t v___x_880_; 
v___x_880_ = l_Lean_Expr_hasSyntheticSorry(v_a_795_);
if (v___x_880_ == 0)
{
v___y_861_ = v_a_770_;
v___y_862_ = v_a_771_;
v___y_863_ = v_a_772_;
v___y_864_ = v_a_773_;
v___y_865_ = v___x_791_;
v___y_866_ = v_a_775_;
goto v___jp_860_;
}
else
{
lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_a_795_);
lean_dec_ref_known(v___x_791_, 3);
v___x_881_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_796_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_795_);
v___x_804_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_795_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_dec_ref(v___y_801_);
lean_dec(v_a_795_);
return v___x_804_;
}
else
{
lean_object* v_a_805_; uint8_t v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
v___x_806_ = l_Lean_Exception_isInterrupt(v_a_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; 
lean_inc(v_a_805_);
v___x_807_ = l_Lean_Exception_isRuntime(v_a_805_);
if (v___x_807_ == 0)
{
if (lean_obj_tag(v_a_805_) == 0)
{
lean_dec_ref_known(v_a_805_, 2);
lean_dec_ref(v___y_801_);
lean_dec(v_a_795_);
return v___x_804_;
}
else
{
lean_object* v_id_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_821_; 
v_id_808_ = lean_ctor_get(v_a_805_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_a_805_, 1);
lean_dec(v_unused_822_);
v___x_810_ = v_a_805_;
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_id_808_);
lean_dec(v_a_805_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = l_Lean_instBEqInternalExceptionId_beq(v___x_803_, v_id_808_);
lean_dec(v_id_808_);
if (v___x_812_ == 0)
{
lean_del_object(v___x_810_);
lean_dec_ref(v___y_801_);
lean_dec(v_a_795_);
return v___x_804_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_813_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6);
v___x_814_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8);
v___x_815_ = l_Lean_indentExpr(v_a_795_);
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 7);
lean_ctor_set(v___x_810_, 1, v___x_815_);
lean_ctor_set(v___x_810_, 0, v___x_814_);
v___x_817_ = v___x_810_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_813_);
v___x_819_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_818_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec_ref(v___y_801_);
return v___x_819_;
}
}
}
}
}
else
{
lean_dec(v_a_805_);
lean_dec_ref(v___y_801_);
lean_dec(v_a_795_);
return v___x_804_;
}
}
else
{
lean_dec(v_a_805_);
lean_dec_ref(v___y_801_);
lean_dec(v_a_795_);
return v___x_804_;
}
}
}
v___jp_823_:
{
lean_object* v___x_830_; 
lean_inc(v_a_795_);
v___x_830_ = l_Lean_Meta_getMVars(v_a_795_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_831_, v___x_779_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v_a_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; uint8_t v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
if (v___x_834_ == 0)
{
v___y_797_ = v___y_824_;
v___y_798_ = v___y_825_;
v___y_799_ = v___y_826_;
v___y_800_ = v___y_827_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_829_;
goto v___jp_796_;
}
else
{
lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v___y_828_);
lean_dec(v_a_795_);
v___x_835_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v___y_828_);
lean_dec(v_a_795_);
v_a_844_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_832_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_832_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___y_828_);
lean_dec(v_a_795_);
v_a_852_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_830_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_830_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
v___jp_860_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v___x_867_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10);
v___x_868_ = l_Lean_indentExpr(v_a_795_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_869_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec_ref(v___y_865_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref_known(v___x_791_, 3);
v_a_890_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_792_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_792_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_stx_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(uint8_t v_config_917_, lean_object* v_item_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_item_927_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_931_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_918_, v___x_930_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_931_) == 0)
{
uint8_t v___x_932_; 
lean_dec_ref_known(v___x_931_, 1);
v___x_932_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_918_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_933_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_918_);
lean_inc_ref(v_item_918_);
v___x_934_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_918_);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1));
v___x_936_ = lean_string_dec_eq(v___x_933_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2));
v___x_938_ = lean_string_dec_eq(v___x_933_, v___x_937_);
lean_dec_ref(v___x_933_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_item_918_);
v_item_927_ = v___x_934_;
goto v___jp_926_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3));
v___x_940_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_918_, v___x_939_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_940_) == 0)
{
uint8_t v___x_941_; 
lean_dec_ref_known(v___x_940_, 1);
v___x_941_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_934_);
if (v___x_941_ == 0)
{
lean_dec_ref(v_item_918_);
v_item_927_ = v___x_934_;
goto v___jp_926_;
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v___x_934_);
v___x_942_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_942_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_942_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___x_934_);
lean_dec_ref(v_item_918_);
v_a_959_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_940_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_940_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
uint8_t v___x_967_; 
lean_dec_ref(v___x_933_);
v___x_967_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_934_);
if (v___x_967_ == 0)
{
lean_dec_ref(v_item_918_);
v_item_927_ = v___x_934_;
goto v___jp_926_;
}
else
{
lean_object* v_value_968_; lean_object* v___x_969_; 
lean_dec_ref(v___x_934_);
v_value_968_ = lean_ctor_get(v_item_918_, 2);
lean_inc(v_value_968_);
lean_dec_ref(v_item_918_);
v___x_969_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_value_968_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_969_;
}
}
}
else
{
v_item_927_ = v_item_918_;
goto v___jp_926_;
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_item_918_);
v_a_970_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_931_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_931_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0));
v___x_929_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_927_, v___x_928_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_978_, lean_object* v_item_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_config_3630__boxed_987_; lean_object* v_res_988_; 
v_config_3630__boxed_987_ = lean_unbox(v_config_978_);
v_res_988_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(v_config_3630__boxed_987_, v_item_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_991_, v___y_995_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(v_e_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1037_, v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1047_, lean_object* v_macroStack_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1047_, v_macroStack_1048_, v___y_1053_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1057_, lean_object* v_macroStack_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1057_, v_macroStack_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_1069_ = l_Lean_mkConst(v___x_1068_, v___x_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(uint8_t v_cfg_1072_, lean_object* v_cfgItem_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1);
v___x_1082_ = lean_box(v_cfg_1072_);
v___x_1083_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_1082_, v_cfgItem_1073_, v___x_1081_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed(lean_object* v_cfg_1084_, lean_object* v_cfgItem_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_cfg_boxed_1093_; lean_object* v_res_1094_; 
v_cfg_boxed_1093_ = lean_unbox(v_cfg_1084_);
v_res_1094_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(v_cfg_boxed_1093_, v_cfgItem_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v_cfgItem_1085_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(lean_object* v_cfg_1096_, uint8_t v_init_1097_, uint8_t v_logExceptions_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_onErr_1103_; lean_object* v_eval_1104_; 
v_onErr_1103_ = ((lean_object*)(l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0));
v_eval_1104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0));
if (v_logExceptions_1098_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(v_init_1097_);
v___x_1106_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1104_, v___x_1105_, v_cfg_1096_, v_onErr_1103_, v_logExceptions_1098_, v_a_1100_, v_a_1101_);
return v___x_1106_;
}
else
{
uint8_t v_recover_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_recover_1107_ = lean_ctor_get_uint8(v_a_1099_, sizeof(void*)*1);
v___x_1108_ = lean_box(v_init_1097_);
v___x_1109_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1104_, v___x_1108_, v_cfg_1096_, v_onErr_1103_, v_recover_1107_, v_a_1100_, v_a_1101_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___boxed(lean_object* v_cfg_1110_, lean_object* v_init_1111_, lean_object* v_logExceptions_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_init_boxed_1117_; uint8_t v_logExceptions_boxed_1118_; lean_object* v_res_1119_; 
v_init_boxed_1117_ = lean_unbox(v_init_1111_);
v_logExceptions_boxed_1118_ = lean_unbox(v_logExceptions_1112_);
v_res_1119_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1110_, v_init_boxed_1117_, v_logExceptions_boxed_1118_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig(lean_object* v_cfg_1120_, uint8_t v_init_1121_, uint8_t v_logExceptions_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1120_, v_init_1121_, v_logExceptions_1122_, v_a_1123_, v_a_1129_, v_a_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___boxed(lean_object* v_cfg_1133_, lean_object* v_init_1134_, lean_object* v_logExceptions_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_init_boxed_1145_; uint8_t v_logExceptions_boxed_1146_; lean_object* v_res_1147_; 
v_init_boxed_1145_ = lean_unbox(v_init_1134_);
v_logExceptions_boxed_1146_ = lean_unbox(v_logExceptions_1135_);
v_res_1147_ = l_Lean_Elab_Tactic_elabImpossibleConfig(v_cfg_1133_, v_init_boxed_1145_, v_logExceptions_boxed_1146_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(lean_object* v_e_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = l_Lean_Expr_hasMVar(v_e_1148_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_e_1148_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v_mctx_1154_; lean_object* v___x_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; lean_object* v_cache_1159_; lean_object* v_zetaDeltaFVarIds_1160_; lean_object* v_postponed_1161_; lean_object* v_diag_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
v___x_1153_ = lean_st_ref_get(v___y_1149_);
v_mctx_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_mctx_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_instantiateMVarsCore(v_mctx_1154_, v_e_1148_);
v_fst_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_snd_1157_);
lean_dec_ref(v___x_1155_);
v___x_1158_ = lean_st_ref_take(v___y_1149_);
v_cache_1159_ = lean_ctor_get(v___x_1158_, 1);
v_zetaDeltaFVarIds_1160_ = lean_ctor_get(v___x_1158_, 2);
v_postponed_1161_ = lean_ctor_get(v___x_1158_, 3);
v_diag_1162_ = lean_ctor_get(v___x_1158_, 4);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v___x_1158_, 0);
lean_dec(v_unused_1172_);
v___x_1164_ = v___x_1158_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_diag_1162_);
lean_inc(v_postponed_1161_);
lean_inc(v_zetaDeltaFVarIds_1160_);
lean_inc(v_cache_1159_);
lean_dec(v___x_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_snd_1157_);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_snd_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_cache_1159_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_zetaDeltaFVarIds_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_postponed_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_diag_1162_);
v___x_1167_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_st_ref_put(v___y_1149_, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_fst_1156_);
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg___boxed(lean_object* v_e_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1173_, v___y_1174_);
lean_dec(v___y_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(lean_object* v_e_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1177_, v___y_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___boxed(lean_object* v_e_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(v_e_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1209_ = lean_apply_9(v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, lean_box(0));
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed(lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(lean_object* v_mvarId_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___f_1232_; lean_object* v___x_1233_; 
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1232_, 0, v_x_1222_);
lean_closure_set(v___f_1232_, 1, v___y_1223_);
lean_closure_set(v___f_1232_, 2, v___y_1224_);
lean_closure_set(v___f_1232_, 3, v___y_1225_);
lean_closure_set(v___f_1232_, 4, v___y_1226_);
v___x_1233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1221_, v___f_1232_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
return v___x_1233_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___boxed(lean_object* v_mvarId_1242_, lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1242_, v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(lean_object* v_00_u03b1_1254_, lean_object* v_mvarId_1255_, lean_object* v_x_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1255_, v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_mvarId_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(v_00_u03b1_1267_, v_mvarId_1268_, v_x_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(lean_object* v_kind_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_auxDeclNGen_1284_; lean_object* v___x_1285_; lean_object* v_env_1286_; lean_object* v___x_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1290_; lean_object* v_env_1291_; lean_object* v_nextMacroScope_1292_; lean_object* v_ngen_1293_; lean_object* v_traceState_1294_; lean_object* v_cache_1295_; lean_object* v_recordedDeps_1296_; lean_object* v_messages_1297_; lean_object* v_infoState_1298_; lean_object* v_snapshotTasks_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1308_; 
v___x_1283_ = lean_st_ref_get(v___y_1281_);
v_auxDeclNGen_1284_ = lean_ctor_get(v___x_1283_, 3);
lean_inc_ref(v_auxDeclNGen_1284_);
lean_dec(v___x_1283_);
v___x_1285_ = lean_st_ref_get(v___y_1281_);
v_env_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_ref(v_env_1286_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_1286_, v_auxDeclNGen_1284_, v_kind_1280_);
v_fst_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec_ref(v___x_1287_);
v___x_1290_ = lean_st_ref_take(v___y_1281_);
v_env_1291_ = lean_ctor_get(v___x_1290_, 0);
v_nextMacroScope_1292_ = lean_ctor_get(v___x_1290_, 1);
v_ngen_1293_ = lean_ctor_get(v___x_1290_, 2);
v_traceState_1294_ = lean_ctor_get(v___x_1290_, 4);
v_cache_1295_ = lean_ctor_get(v___x_1290_, 5);
v_recordedDeps_1296_ = lean_ctor_get(v___x_1290_, 6);
v_messages_1297_ = lean_ctor_get(v___x_1290_, 7);
v_infoState_1298_ = lean_ctor_get(v___x_1290_, 8);
v_snapshotTasks_1299_ = lean_ctor_get(v___x_1290_, 9);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1290_, 3);
lean_dec(v_unused_1309_);
v___x_1301_ = v___x_1290_;
v_isShared_1302_ = v_isSharedCheck_1308_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snapshotTasks_1299_);
lean_inc(v_infoState_1298_);
lean_inc(v_messages_1297_);
lean_inc(v_recordedDeps_1296_);
lean_inc(v_cache_1295_);
lean_inc(v_traceState_1294_);
lean_inc(v_ngen_1293_);
lean_inc(v_nextMacroScope_1292_);
lean_inc(v_env_1291_);
lean_dec(v___x_1290_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1308_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 3, v_snd_1289_);
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_env_1291_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_nextMacroScope_1292_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_ngen_1293_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_snd_1289_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_traceState_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 5, v_cache_1295_);
lean_ctor_set(v_reuseFailAlloc_1307_, 6, v_recordedDeps_1296_);
lean_ctor_set(v_reuseFailAlloc_1307_, 7, v_messages_1297_);
lean_ctor_set(v_reuseFailAlloc_1307_, 8, v_infoState_1298_);
lean_ctor_set(v_reuseFailAlloc_1307_, 9, v_snapshotTasks_1299_);
v___x_1304_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_st_ref_put(v___y_1281_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_fst_1288_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg___boxed(lean_object* v_kind_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1310_, v___y_1311_);
lean_dec(v___y_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(lean_object* v_kind_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1314_, v___y_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___boxed(lean_object* v_kind_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(v_kind_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4(lean_object* v_opts_1336_, lean_object* v_opt_1337_){
_start:
{
lean_object* v_name_1338_; lean_object* v_defValue_1339_; lean_object* v_map_1340_; lean_object* v___x_1341_; 
v_name_1338_ = lean_ctor_get(v_opt_1337_, 0);
v_defValue_1339_ = lean_ctor_get(v_opt_1337_, 1);
v_map_1340_ = lean_ctor_get(v_opts_1336_, 0);
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1340_, v_name_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_inc(v_defValue_1339_);
return v_defValue_1339_;
}
else
{
lean_object* v_val_1342_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v___x_1341_, 1);
if (lean_obj_tag(v_val_1342_) == 3)
{
lean_object* v_v_1343_; 
v_v_1343_ = lean_ctor_get(v_val_1342_, 0);
lean_inc(v_v_1343_);
lean_dec_ref_known(v_val_1342_, 1);
return v_v_1343_;
}
else
{
lean_dec(v_val_1342_);
lean_inc(v_defValue_1339_);
return v_defValue_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(lean_object* v_opts_1344_, lean_object* v_opt_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v_opts_1344_, v_opt_1345_);
lean_dec_ref(v_opt_1345_);
lean_dec_ref(v_opts_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0(lean_object* v_a_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_MVarId_getType(v_a_1347_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_a_1358_, v___y_1353_);
return v___x_1359_;
}
else
{
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(lean_object* v_a_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Elab_Tactic_evalImpossible___lam__0(v_a_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1(lean_object* v_a_1371_, lean_object* v_trees_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
v___x_1382_ = lean_apply_9(v_a_1371_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, lean_box(0));
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1383_);
lean_ctor_set(v___x_1387_, 1, v_trees_1372_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_trees_1372_);
v_a_1392_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1382_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1382_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(lean_object* v_a_1400_, lean_object* v_trees_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Elab_Tactic_evalImpossible___lam__1(v_a_1400_, v_trees_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6(lean_object* v_o_1415_, lean_object* v_k_1416_, uint8_t v_v_1417_){
_start:
{
lean_object* v_map_1418_; uint8_t v_hasTrace_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1433_; 
v_map_1418_ = lean_ctor_get(v_o_1415_, 0);
v_hasTrace_1419_ = lean_ctor_get_uint8(v_o_1415_, sizeof(void*)*1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_o_1415_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1421_ = v_o_1415_;
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_map_1418_);
lean_dec(v_o_1415_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1423_, 0, v_v_1417_);
lean_inc(v_k_1416_);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1416_, v___x_1423_, v_map_1418_);
if (v_hasTrace_1419_ == 0)
{
lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___closed__1));
v___x_1426_ = l_Lean_Name_isPrefixOf(v___x_1425_, v_k_1416_);
lean_dec(v_k_1416_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1428_ = v___x_1421_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1424_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*1, v___x_1426_);
return v___x_1428_;
}
}
else
{
lean_object* v___x_1431_; 
lean_dec(v_k_1416_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*1, v_hasTrace_1419_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6___boxed(lean_object* v_o_1434_, lean_object* v_k_1435_, lean_object* v_v_1436_){
_start:
{
uint8_t v_v_boxed_1437_; lean_object* v_res_1438_; 
v_v_boxed_1437_ = lean_unbox(v_v_1436_);
v_res_1438_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6(v_o_1434_, v_k_1435_, v_v_boxed_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5(lean_object* v_opts_1439_, lean_object* v_opt_1440_, uint8_t v_val_1441_){
_start:
{
lean_object* v_name_1442_; lean_object* v___x_1443_; 
v_name_1442_ = lean_ctor_get(v_opt_1440_, 0);
lean_inc(v_name_1442_);
lean_dec_ref(v_opt_1440_);
v___x_1443_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5_spec__6(v_opts_1439_, v_name_1442_, v_val_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(lean_object* v_opts_1444_, lean_object* v_opt_1445_, lean_object* v_val_1446_){
_start:
{
uint8_t v_val_boxed_1447_; lean_object* v_res_1448_; 
v_val_boxed_1447_ = lean_unbox(v_val_1446_);
v_res_1448_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v_opts_1444_, v_opt_1445_, v_val_boxed_1447_);
return v_res_1448_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(32u);
v___x_1450_ = lean_mk_empty_array_with_capacity(v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1452_ = ((size_t)5ULL);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_unsigned_to_nat(32u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0);
v___x_1457_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v___x_1455_);
lean_ctor_set(v___x_1457_, 2, v___x_1453_);
lean_ctor_set(v___x_1457_, 3, v___x_1453_);
lean_ctor_set_usize(v___x_1457_, 4, v___x_1452_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v_infoState_1461_; lean_object* v_trees_1462_; lean_object* v___x_1463_; lean_object* v_infoState_1464_; lean_object* v_env_1465_; lean_object* v_nextMacroScope_1466_; lean_object* v_ngen_1467_; lean_object* v_auxDeclNGen_1468_; lean_object* v_traceState_1469_; lean_object* v_cache_1470_; lean_object* v_recordedDeps_1471_; lean_object* v_messages_1472_; lean_object* v_snapshotTasks_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1494_; 
v___x_1460_ = lean_st_ref_get(v___y_1458_);
v_infoState_1461_ = lean_ctor_get(v___x_1460_, 8);
lean_inc_ref(v_infoState_1461_);
lean_dec(v___x_1460_);
v_trees_1462_ = lean_ctor_get(v_infoState_1461_, 2);
lean_inc_ref(v_trees_1462_);
lean_dec_ref(v_infoState_1461_);
v___x_1463_ = lean_st_ref_take(v___y_1458_);
v_infoState_1464_ = lean_ctor_get(v___x_1463_, 8);
v_env_1465_ = lean_ctor_get(v___x_1463_, 0);
v_nextMacroScope_1466_ = lean_ctor_get(v___x_1463_, 1);
v_ngen_1467_ = lean_ctor_get(v___x_1463_, 2);
v_auxDeclNGen_1468_ = lean_ctor_get(v___x_1463_, 3);
v_traceState_1469_ = lean_ctor_get(v___x_1463_, 4);
v_cache_1470_ = lean_ctor_get(v___x_1463_, 5);
v_recordedDeps_1471_ = lean_ctor_get(v___x_1463_, 6);
v_messages_1472_ = lean_ctor_get(v___x_1463_, 7);
v_snapshotTasks_1473_ = lean_ctor_get(v___x_1463_, 9);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1475_ = v___x_1463_;
v_isShared_1476_ = v_isSharedCheck_1494_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snapshotTasks_1473_);
lean_inc(v_infoState_1464_);
lean_inc(v_messages_1472_);
lean_inc(v_recordedDeps_1471_);
lean_inc(v_cache_1470_);
lean_inc(v_traceState_1469_);
lean_inc(v_auxDeclNGen_1468_);
lean_inc(v_ngen_1467_);
lean_inc(v_nextMacroScope_1466_);
lean_inc(v_env_1465_);
lean_dec(v___x_1463_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1494_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
uint8_t v_enabled_1477_; lean_object* v_assignment_1478_; lean_object* v_lazyAssignment_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1492_; 
v_enabled_1477_ = lean_ctor_get_uint8(v_infoState_1464_, sizeof(void*)*3);
v_assignment_1478_ = lean_ctor_get(v_infoState_1464_, 0);
v_lazyAssignment_1479_ = lean_ctor_get(v_infoState_1464_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_infoState_1464_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_infoState_1464_, 2);
lean_dec(v_unused_1493_);
v___x_1481_ = v_infoState_1464_;
v_isShared_1482_ = v_isSharedCheck_1492_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_lazyAssignment_1479_);
lean_inc(v_assignment_1478_);
lean_dec(v_infoState_1464_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1492_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 2, v___x_1483_);
v___x_1485_ = v___x_1481_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_assignment_1478_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_lazyAssignment_1479_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v___x_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*3, v_enabled_1477_);
v___x_1485_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 8, v___x_1485_);
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_env_1465_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_nextMacroScope_1466_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_ngen_1467_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_auxDeclNGen_1468_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_traceState_1469_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_cache_1470_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_recordedDeps_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_messages_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1490_, 9, v_snapshotTasks_1473_);
v___x_1487_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_st_ref_put(v___y_1458_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_trees_1462_);
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___boxed(lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1495_);
lean_dec(v___y_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(lean_object* v___y_1498_, lean_object* v_mkInfoTree_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v_a_1507_, lean_object* v_a_x3f_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_infoState_1511_; lean_object* v_trees_1512_; lean_object* v___x_1513_; 
v___x_1510_ = lean_st_ref_get(v___y_1498_);
v_infoState_1511_ = lean_ctor_get(v___x_1510_, 8);
lean_inc_ref(v_infoState_1511_);
lean_dec(v___x_1510_);
v_trees_1512_ = lean_ctor_get(v_infoState_1511_, 2);
lean_inc_ref(v_trees_1512_);
lean_dec_ref(v_infoState_1511_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
v___x_1513_ = lean_apply_10(v_mkInfoTree_1499_, v_trees_1512_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1498_, lean_box(0));
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1553_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1553_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1553_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v_infoState_1519_; lean_object* v_env_1520_; lean_object* v_nextMacroScope_1521_; lean_object* v_ngen_1522_; lean_object* v_auxDeclNGen_1523_; lean_object* v_traceState_1524_; lean_object* v_cache_1525_; lean_object* v_recordedDeps_1526_; lean_object* v_messages_1527_; lean_object* v_snapshotTasks_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1552_; 
v___x_1518_ = lean_st_ref_take(v___y_1498_);
v_infoState_1519_ = lean_ctor_get(v___x_1518_, 8);
v_env_1520_ = lean_ctor_get(v___x_1518_, 0);
v_nextMacroScope_1521_ = lean_ctor_get(v___x_1518_, 1);
v_ngen_1522_ = lean_ctor_get(v___x_1518_, 2);
v_auxDeclNGen_1523_ = lean_ctor_get(v___x_1518_, 3);
v_traceState_1524_ = lean_ctor_get(v___x_1518_, 4);
v_cache_1525_ = lean_ctor_get(v___x_1518_, 5);
v_recordedDeps_1526_ = lean_ctor_get(v___x_1518_, 6);
v_messages_1527_ = lean_ctor_get(v___x_1518_, 7);
v_snapshotTasks_1528_ = lean_ctor_get(v___x_1518_, 9);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1530_ = v___x_1518_;
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snapshotTasks_1528_);
lean_inc(v_infoState_1519_);
lean_inc(v_messages_1527_);
lean_inc(v_recordedDeps_1526_);
lean_inc(v_cache_1525_);
lean_inc(v_traceState_1524_);
lean_inc(v_auxDeclNGen_1523_);
lean_inc(v_ngen_1522_);
lean_inc(v_nextMacroScope_1521_);
lean_inc(v_env_1520_);
lean_dec(v___x_1518_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
uint8_t v_enabled_1532_; lean_object* v_assignment_1533_; lean_object* v_lazyAssignment_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1550_; 
v_enabled_1532_ = lean_ctor_get_uint8(v_infoState_1519_, sizeof(void*)*3);
v_assignment_1533_ = lean_ctor_get(v_infoState_1519_, 0);
v_lazyAssignment_1534_ = lean_ctor_get(v_infoState_1519_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_infoState_1519_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_infoState_1519_, 2);
lean_dec(v_unused_1551_);
v___x_1536_ = v_infoState_1519_;
v_isShared_1537_ = v_isSharedCheck_1550_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_lazyAssignment_1534_);
lean_inc(v_assignment_1533_);
lean_dec(v_infoState_1519_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1550_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_box(0);
v___x_1539_ = l_Lean_PersistentArray_push___redArg(v_a_1507_, v_a_1514_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 2, v___x_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_assignment_1533_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_lazyAssignment_1534_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v___x_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*3, v_enabled_1532_);
v___x_1541_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 8, v___x_1541_);
v___x_1543_ = v___x_1530_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_env_1520_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_nextMacroScope_1521_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_ngen_1522_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_auxDeclNGen_1523_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_traceState_1524_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_cache_1525_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_recordedDeps_1526_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_messages_1527_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1548_, 9, v_snapshotTasks_1528_);
v___x_1543_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_st_ref_put(v___y_1498_, v___x_1543_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1538_);
v___x_1546_ = v___x_1516_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1538_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v_a_1507_);
v_a_1554_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1513_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1513_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0___boxed(lean_object* v___y_1562_, lean_object* v_mkInfoTree_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v_a_1571_, lean_object* v_a_x3f_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1562_, v_mkInfoTree_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v_a_1571_, v_a_x3f_1572_);
lean_dec(v_a_x3f_1572_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1562_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(lean_object* v_x_1575_, lean_object* v_mkInfoTree_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v_infoState_1587_; uint8_t v_enabled_1588_; 
v___x_1586_ = lean_st_ref_get(v___y_1584_);
v_infoState_1587_ = lean_ctor_get(v___x_1586_, 8);
lean_inc_ref(v_infoState_1587_);
lean_dec(v___x_1586_);
v_enabled_1588_ = lean_ctor_get_uint8(v_infoState_1587_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1587_);
if (v_enabled_1588_ == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref(v_mkInfoTree_1576_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v___x_1589_ = lean_apply_9(v_x_1575_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, lean_box(0));
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v_a_1591_; lean_object* v_r_1592_; 
v___x_1590_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1584_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v_r_1592_ = lean_apply_9(v_x_1575_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, lean_box(0));
if (lean_obj_tag(v_r_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1617_; 
v_a_1593_ = lean_ctor_get(v_r_1592_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_r_1592_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1595_ = v_r_1592_;
v_isShared_1596_ = v_isSharedCheck_1617_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v_r_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1617_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
lean_inc(v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1584_, v_mkInfoTree_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v_a_1591_, v___x_1598_);
lean_dec_ref(v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_a_1593_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1593_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1593_);
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v_r_1592_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v_r_1592_, 1);
v___x_1619_ = lean_box(0);
v___x_1620_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1584_, v_mkInfoTree_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v_a_1591_, v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1628_);
v___x_1622_ = v___x_1620_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v___x_1620_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 1);
lean_ctor_set(v___x_1622_, 0, v_a_1618_);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1618_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1618_);
v_a_1629_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1620_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1620_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___boxed(lean_object* v_x_1637_, lean_object* v_mkInfoTree_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_1637_, v_mkInfoTree_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(lean_object* v_msg_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_ref_1655_; lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
v_ref_1655_ = lean_ctor_get(v___y_1652_, 2);
v___x_1656_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_inc(v_ref_1655_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_ref_1655_);
lean_ctor_set(v___x_1661_, 1, v_a_1657_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(lean_object* v_ref_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_toCold_1684_; lean_object* v_currRecDepth_1685_; lean_object* v_ref_1686_; uint16_t v_optionFlags_1687_; uint8_t v_suppressElabErrors_1688_; uint8_t v_isRecordingDeps_1689_; lean_object* v_ref_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_toCold_1684_ = lean_ctor_get(v___y_1681_, 0);
v_currRecDepth_1685_ = lean_ctor_get(v___y_1681_, 1);
v_ref_1686_ = lean_ctor_get(v___y_1681_, 2);
v_optionFlags_1687_ = lean_ctor_get_uint16(v___y_1681_, sizeof(void*)*3);
v_suppressElabErrors_1688_ = lean_ctor_get_uint8(v___y_1681_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1689_ = lean_ctor_get_uint8(v___y_1681_, sizeof(void*)*3 + 3);
v_ref_1690_ = l_Lean_replaceRef(v_ref_1673_, v_ref_1686_);
lean_inc(v_currRecDepth_1685_);
lean_inc_ref(v_toCold_1684_);
v___x_1691_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1691_, 0, v_toCold_1684_);
lean_ctor_set(v___x_1691_, 1, v_currRecDepth_1685_);
lean_ctor_set(v___x_1691_, 2, v_ref_1690_);
lean_ctor_set_uint16(v___x_1691_, sizeof(void*)*3, v_optionFlags_1687_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*3 + 2, v_suppressElabErrors_1688_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*3 + 3, v_isRecordingDeps_1689_);
v___x_1692_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1674_, v___y_1679_, v___y_1680_, v___x_1691_, v___y_1682_);
lean_dec_ref_known(v___x_1691_, 3);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg___boxed(lean_object* v_ref_1693_, lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_1693_, v_msg_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v_ref_1693_);
return v_res_1704_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__0(void){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__1(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__0, &l_Lean_Elab_Tactic_evalImpossible___closed__0_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__0);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__2(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__1, &l_Lean_Elab_Tactic_evalImpossible___closed__1_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__1);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__3(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__0, &l_Lean_Elab_Tactic_evalImpossible___closed__0_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__0);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__4(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_unsigned_to_nat(32u);
v___x_1713_ = lean_mk_empty_array_with_capacity(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__5(void){
_start:
{
size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = ((size_t)5ULL);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_unsigned_to_nat(32u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__4, &l_Lean_Elab_Tactic_evalImpossible___closed__4_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__4);
v___x_1720_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___x_1718_);
lean_ctor_set(v___x_1720_, 2, v___x_1716_);
lean_ctor_set(v___x_1720_, 3, v___x_1716_);
lean_ctor_set_usize(v___x_1720_, 4, v___x_1715_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__6(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_box(1);
v___x_1722_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__5, &l_Lean_Elab_Tactic_evalImpossible___closed__5_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__5);
v___x_1723_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__3, &l_Lean_Elab_Tactic_evalImpossible___closed__3_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__3);
v___x_1724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1722_);
lean_ctor_set(v___x_1724_, 2, v___x_1721_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__11(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__10));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible(lean_object* v_stx_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v_a_1746_; lean_object* v___x_1756_; lean_object* v_kw_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; uint16_t v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; uint16_t v___y_1808_; uint8_t v___x_1830_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___x_1846_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v_kw_1757_ = l_Lean_Syntax_getArg(v_stx_1733_, v___x_1756_);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = l_Lean_Syntax_getArg(v_stx_1733_, v___x_1758_);
v___x_1760_ = 0;
v___x_1830_ = 1;
v___x_1846_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v___x_1759_, v___x_1760_, v___x_1830_, v_a_1734_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = lean_unsigned_to_nat(2u);
v___x_1849_ = l_Lean_Syntax_getArg(v_stx_1733_, v___x_1848_);
v___x_1850_ = lean_unsigned_to_nat(3u);
v___x_1851_ = l_Lean_Syntax_getArg(v_stx_1733_, v___x_1850_);
v___x_1852_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1735_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___f_1854_; lean_object* v___x_1855_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc_n(v_a_1853_, 3);
lean_dec_ref_known(v___x_1852_, 1);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1854_, 0, v_a_1853_);
v___x_1855_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_a_1853_, v___f_1854_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; uint8_t v___x_1975_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1975_ = l_Lean_Expr_hasLevelMVar(v_a_1856_);
if (v___x_1975_ == 0)
{
lean_dec(v_kw_1757_);
v___y_1858_ = v_a_1734_;
v___y_1859_ = v_a_1735_;
v___y_1860_ = v_a_1736_;
v___y_1861_ = v_a_1737_;
v___y_1862_ = v_a_1738_;
v___y_1863_ = v_a_1739_;
v___y_1864_ = v_a_1740_;
v___y_1865_ = v_a_1741_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec(v_a_1853_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
lean_dec(v_a_1847_);
v___x_1976_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__11, &l_Lean_Elab_Tactic_evalImpossible___closed__11_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__11);
v___x_1977_ = l_Lean_indentExpr(v_a_1856_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_kw_1757_, v___x_1978_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_kw_1757_);
return v___x_1979_;
}
v___jp_1857_:
{
uint8_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_unbox(v_a_1847_);
lean_dec(v_a_1847_);
lean_inc(v_a_1853_);
v___x_1867_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(v_a_1853_, v_a_1856_, v___x_1866_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1966_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v_fst_1869_ = lean_ctor_get(v_a_1868_, 0);
v_snd_1870_ = lean_ctor_get(v_a_1868_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_a_1868_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1872_ = v_a_1868_;
v_isShared_1873_ = v_isSharedCheck_1966_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_inc(v_fst_1869_);
lean_dec(v_a_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1966_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Elab_admitGoal(v_a_1853_, v___x_1830_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1875_; 
lean_dec_ref_known(v___x_1874_, 1);
v___x_1875_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1877_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__6, &l_Lean_Elab_Tactic_evalImpossible___closed__6_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__6);
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__7));
v___x_1879_ = 2;
v___x_1880_ = lean_box(0);
lean_inc(v_fst_1869_);
v___x_1881_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1877_, v___x_1878_, v_fst_1869_, v___x_1879_, v___x_1880_, v___x_1756_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = l_Lean_Expr_mvarId_x21(v_a_1882_);
lean_dec(v_a_1882_);
v___x_1884_ = lean_array_get_size(v_snd_1870_);
v___x_1885_ = lean_array_to_list(v_snd_1870_);
lean_inc(v___x_1883_);
v___x_1886_ = l_Lean_Meta_introNCore(v___x_1883_, v___x_1884_, v___x_1885_, v___x_1760_, v___x_1760_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_snd_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1940_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v_snd_1888_ = lean_ctor_get(v_a_1887_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_a_1887_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_a_1887_, 0);
lean_dec(v_unused_1941_);
v___x_1890_ = v_a_1887_;
v_isShared_1891_ = v_isSharedCheck_1940_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1888_);
lean_dec(v_a_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1940_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 1);
lean_ctor_set(v___x_1890_, 1, v___x_1892_);
lean_ctor_set(v___x_1890_, 0, v_snd_1888_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_snd_1888_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_1894_, v___y_1859_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1896_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1896_, 0, v___x_1851_);
v___x_1897_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_1849_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed), 11, 1);
lean_closure_set(v___f_1899_, 0, v_a_1898_);
v___x_1900_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v___x_1896_, v___f_1899_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1901_ = l_Lean_Elab_Tactic_done(v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_a_1904_; lean_object* v___x_1905_; lean_object* v_a_1906_; lean_object* v___x_1907_; 
lean_dec_ref_known(v___x_1901_, 1);
v___x_1902_ = l_Lean_mkMVar(v___x_1883_);
v___x_1903_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v___x_1902_, v___y_1863_);
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_fst_1869_, v___y_1863_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_a_1906_, v_a_1904_, v___x_1760_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_toCold_1911_; lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1933_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__9));
v___x_1910_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v___x_1909_, v___y_1865_);
v_toCold_1911_ = lean_ctor_get(v___y_1864_, 0);
v_a_1912_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1914_ = v___x_1910_;
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_levelParams_1916_; lean_object* v_type_1917_; lean_object* v_value_1918_; uint8_t v_isRecordingDeps_1919_; lean_object* v_options_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v_levelParams_1916_ = lean_ctor_get(v_a_1908_, 0);
lean_inc_ref(v_levelParams_1916_);
v_type_1917_ = lean_ctor_get(v_a_1908_, 1);
lean_inc_ref(v_type_1917_);
v_value_1918_ = lean_ctor_get(v_a_1908_, 2);
lean_inc_ref(v_value_1918_);
lean_dec(v_a_1908_);
v_isRecordingDeps_1919_ = lean_ctor_get_uint8(v___y_1864_, sizeof(void*)*3 + 3);
v_options_1920_ = lean_ctor_get(v_toCold_1911_, 2);
v___x_1921_ = lean_array_to_list(v_levelParams_1916_);
lean_inc(v_a_1912_);
v___x_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1912_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_ctor_set(v___x_1922_, 2, v_type_1917_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
lean_ctor_set(v___x_1872_, 1, v___x_1892_);
lean_ctor_set(v___x_1872_, 0, v_a_1912_);
v___x_1924_ = v___x_1872_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1912_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1892_);
v___x_1924_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1922_);
lean_ctor_set(v___x_1925_, 1, v_value_1918_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 2);
lean_ctor_set(v___x_1914_, 0, v___x_1925_);
v___x_1927_ = v___x_1914_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
if (v_isRecordingDeps_1919_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = l_Lean_Elab_async;
lean_inc_ref(v_options_1920_);
v___x_1929_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v_options_1920_, v___x_1928_, v___x_1760_);
v___y_1832_ = v___y_1865_;
v___y_1833_ = v_a_1876_;
v___y_1834_ = v___y_1864_;
v___y_1835_ = v___x_1927_;
v___y_1836_ = v___y_1859_;
v___y_1837_ = v___x_1929_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1930_; 
lean_inc_ref(v_options_1920_);
v___x_1930_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1920_);
v___y_1832_ = v___y_1865_;
v___y_1833_ = v_a_1876_;
v___y_1834_ = v___y_1864_;
v___y_1835_ = v___x_1927_;
v___y_1836_ = v___y_1859_;
v___y_1837_ = v___x_1930_;
goto v___jp_1831_;
}
}
}
}
}
else
{
lean_object* v_a_1934_; 
lean_del_object(v___x_1872_);
v_a_1934_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1907_, 1);
v___y_1744_ = v_a_1876_;
v___y_1745_ = v___y_1859_;
v_a_1746_ = v_a_1934_;
goto v___jp_1743_;
}
}
else
{
lean_object* v_a_1935_; 
lean_dec(v___x_1883_);
lean_del_object(v___x_1872_);
lean_dec(v_fst_1869_);
v_a_1935_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1901_, 1);
v___y_1744_ = v_a_1876_;
v___y_1745_ = v___y_1859_;
v_a_1746_ = v_a_1935_;
goto v___jp_1743_;
}
}
else
{
lean_object* v_a_1936_; 
lean_dec(v___x_1883_);
lean_del_object(v___x_1872_);
lean_dec(v_fst_1869_);
v_a_1936_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1900_, 1);
v___y_1744_ = v_a_1876_;
v___y_1745_ = v___y_1859_;
v_a_1746_ = v_a_1936_;
goto v___jp_1743_;
}
}
else
{
lean_object* v_a_1937_; 
lean_dec_ref(v___x_1896_);
lean_dec(v___x_1883_);
lean_del_object(v___x_1872_);
lean_dec(v_fst_1869_);
v_a_1937_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1897_, 1);
v___y_1744_ = v_a_1876_;
v___y_1745_ = v___y_1859_;
v_a_1746_ = v_a_1937_;
goto v___jp_1743_;
}
}
else
{
lean_object* v_a_1938_; 
lean_dec(v___x_1883_);
lean_del_object(v___x_1872_);
lean_dec(v_fst_1869_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
v_a_1938_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1895_, 1);
v___y_1744_ = v_a_1876_;
v___y_1745_ = v___y_1859_;
v_a_1746_ = v_a_1938_;
goto v___jp_1743_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v___x_1883_);
lean_dec(v_a_1876_);
lean_del_object(v___x_1872_);
lean_dec(v_fst_1869_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
v_a_1942_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1886_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1886_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1876_);
lean_del_object(v___x_1872_);
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
v_a_1950_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1881_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1881_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_del_object(v___x_1872_);
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
v_a_1958_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1875_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1875_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_del_object(v___x_1872_);
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1853_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
v_a_1967_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1867_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1867_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1853_);
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
lean_dec(v_a_1847_);
lean_dec(v_kw_1757_);
v_a_1980_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1855_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1855_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v___x_1851_);
lean_dec(v___x_1849_);
lean_dec(v_a_1847_);
lean_dec(v_kw_1757_);
v_a_1988_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1852_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1852_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_kw_1757_);
v_a_1996_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1846_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1846_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
v___jp_1743_:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1747_, 0);
lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1747_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_dec(v___x_1747_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 1);
lean_ctor_set(v___x_1749_, 0, v_a_1746_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1746_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_dec_ref(v_a_1746_);
return v___x_1747_;
}
}
v___jp_1761_:
{
lean_object* v_toCold_1769_; lean_object* v_currRecDepth_1770_; lean_object* v_ref_1771_; uint8_t v_suppressElabErrors_1772_; uint8_t v_isRecordingDeps_1773_; lean_object* v_fileName_1774_; lean_object* v_fileMap_1775_; lean_object* v_currNamespace_1776_; lean_object* v_openDecls_1777_; lean_object* v_initHeartbeats_1778_; lean_object* v_maxHeartbeats_1779_; lean_object* v_quotContext_1780_; lean_object* v_currMacroScope_1781_; lean_object* v_cancelTk_x3f_1782_; lean_object* v_inheritedTraceOptions_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_toCold_1769_ = lean_ctor_get(v___y_1767_, 0);
v_currRecDepth_1770_ = lean_ctor_get(v___y_1767_, 1);
v_ref_1771_ = lean_ctor_get(v___y_1767_, 2);
v_suppressElabErrors_1772_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1773_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*3 + 3);
v_fileName_1774_ = lean_ctor_get(v_toCold_1769_, 0);
v_fileMap_1775_ = lean_ctor_get(v_toCold_1769_, 1);
v_currNamespace_1776_ = lean_ctor_get(v_toCold_1769_, 4);
v_openDecls_1777_ = lean_ctor_get(v_toCold_1769_, 5);
v_initHeartbeats_1778_ = lean_ctor_get(v_toCold_1769_, 6);
v_maxHeartbeats_1779_ = lean_ctor_get(v_toCold_1769_, 7);
v_quotContext_1780_ = lean_ctor_get(v_toCold_1769_, 8);
v_currMacroScope_1781_ = lean_ctor_get(v_toCold_1769_, 9);
v_cancelTk_x3f_1782_ = lean_ctor_get(v_toCold_1769_, 10);
v_inheritedTraceOptions_1783_ = lean_ctor_get(v_toCold_1769_, 11);
v___x_1784_ = l_Lean_maxRecDepth;
v___x_1785_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v___y_1763_, v___x_1784_);
lean_inc_ref(v_inheritedTraceOptions_1783_);
lean_inc(v_cancelTk_x3f_1782_);
lean_inc(v_currMacroScope_1781_);
lean_inc(v_quotContext_1780_);
lean_inc(v_maxHeartbeats_1779_);
lean_inc(v_initHeartbeats_1778_);
lean_inc(v_openDecls_1777_);
lean_inc(v_currNamespace_1776_);
lean_inc_ref(v_fileMap_1775_);
lean_inc_ref(v_fileName_1774_);
v___x_1786_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1786_, 0, v_fileName_1774_);
lean_ctor_set(v___x_1786_, 1, v_fileMap_1775_);
lean_ctor_set(v___x_1786_, 2, v___y_1763_);
lean_ctor_set(v___x_1786_, 3, v___x_1785_);
lean_ctor_set(v___x_1786_, 4, v_currNamespace_1776_);
lean_ctor_set(v___x_1786_, 5, v_openDecls_1777_);
lean_ctor_set(v___x_1786_, 6, v_initHeartbeats_1778_);
lean_ctor_set(v___x_1786_, 7, v_maxHeartbeats_1779_);
lean_ctor_set(v___x_1786_, 8, v_quotContext_1780_);
lean_ctor_set(v___x_1786_, 9, v_currMacroScope_1781_);
lean_ctor_set(v___x_1786_, 10, v_cancelTk_x3f_1782_);
lean_ctor_set(v___x_1786_, 11, v_inheritedTraceOptions_1783_);
lean_inc(v_ref_1771_);
lean_inc(v_currRecDepth_1770_);
v___x_1787_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v_currRecDepth_1770_);
lean_ctor_set(v___x_1787_, 2, v_ref_1771_);
lean_ctor_set_uint16(v___x_1787_, sizeof(void*)*3, v___y_1766_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 2, v_suppressElabErrors_1772_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 3, v_isRecordingDeps_1773_);
v___x_1788_ = l_Lean_addDecl(v___y_1764_, v___x_1760_, v___x_1787_, v___y_1768_);
lean_dec_ref_known(v___x_1787_, 3);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1762_, v___y_1765_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1798_);
v___x_1792_ = v___x_1790_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v___x_1790_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_a_1789_);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1789_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_dec(v_a_1789_);
return v___x_1790_;
}
}
else
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1788_, 1);
v___y_1744_ = v___y_1762_;
v___y_1745_ = v___y_1765_;
v_a_1746_ = v_a_1799_;
goto v___jp_1743_;
}
}
v___jp_1800_:
{
lean_object* v___x_1809_; lean_object* v_env_1810_; lean_object* v_nextMacroScope_1811_; lean_object* v_ngen_1812_; lean_object* v_auxDeclNGen_1813_; lean_object* v_traceState_1814_; lean_object* v_recordedDeps_1815_; lean_object* v_messages_1816_; lean_object* v_infoState_1817_; lean_object* v_snapshotTasks_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v___x_1809_ = lean_st_ref_take(v___y_1801_);
v_env_1810_ = lean_ctor_get(v___x_1809_, 0);
v_nextMacroScope_1811_ = lean_ctor_get(v___x_1809_, 1);
v_ngen_1812_ = lean_ctor_get(v___x_1809_, 2);
v_auxDeclNGen_1813_ = lean_ctor_get(v___x_1809_, 3);
v_traceState_1814_ = lean_ctor_get(v___x_1809_, 4);
v_recordedDeps_1815_ = lean_ctor_get(v___x_1809_, 6);
v_messages_1816_ = lean_ctor_get(v___x_1809_, 7);
v_infoState_1817_ = lean_ctor_get(v___x_1809_, 8);
v_snapshotTasks_1818_ = lean_ctor_get(v___x_1809_, 9);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1809_, 5);
lean_dec(v_unused_1829_);
v___x_1820_ = v___x_1809_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snapshotTasks_1818_);
lean_inc(v_infoState_1817_);
lean_inc(v_messages_1816_);
lean_inc(v_recordedDeps_1815_);
lean_inc(v_traceState_1814_);
lean_inc(v_auxDeclNGen_1813_);
lean_inc(v_ngen_1812_);
lean_inc(v_nextMacroScope_1811_);
lean_inc(v_env_1810_);
lean_dec(v___x_1809_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = l_Lean_Kernel_enableDiag(v_env_1810_, v___y_1803_);
v___x_1823_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__2, &l_Lean_Elab_Tactic_evalImpossible___closed__2_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__2);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 5, v___x_1823_);
lean_ctor_set(v___x_1820_, 0, v___x_1822_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_nextMacroScope_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_ngen_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_auxDeclNGen_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_traceState_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_recordedDeps_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_messages_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_infoState_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 9, v_snapshotTasks_1818_);
v___x_1825_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_st_ref_put(v___y_1801_, v___x_1825_);
v___y_1762_ = v___y_1802_;
v___y_1763_ = v___y_1804_;
v___y_1764_ = v___y_1806_;
v___y_1765_ = v___y_1807_;
v___y_1766_ = v___y_1808_;
v___y_1767_ = v___y_1805_;
v___y_1768_ = v___y_1801_;
goto v___jp_1761_;
}
}
}
v___jp_1831_:
{
uint16_t v___x_1838_; lean_object* v___x_1839_; lean_object* v_env_1840_; uint8_t v___x_1841_; uint16_t v___x_1842_; uint16_t v___x_1843_; uint16_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1838_ = l_Lean_OptionFlags_ofOptions(v___y_1837_);
v___x_1839_ = lean_st_ref_get(v___y_1832_);
v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1839_);
v___x_1841_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1840_);
lean_dec_ref(v_env_1840_);
v___x_1842_ = 512;
v___x_1843_ = lean_uint16_land(v___x_1838_, v___x_1842_);
v___x_1844_ = 0;
v___x_1845_ = lean_uint16_dec_eq(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
if (v___x_1841_ == 0)
{
v___y_1801_ = v___y_1832_;
v___y_1802_ = v___y_1833_;
v___y_1803_ = v___x_1830_;
v___y_1804_ = v___y_1837_;
v___y_1805_ = v___y_1834_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1836_;
v___y_1808_ = v___x_1838_;
goto v___jp_1800_;
}
else
{
v___y_1762_ = v___y_1833_;
v___y_1763_ = v___y_1837_;
v___y_1764_ = v___y_1835_;
v___y_1765_ = v___y_1836_;
v___y_1766_ = v___x_1838_;
v___y_1767_ = v___y_1834_;
v___y_1768_ = v___y_1832_;
goto v___jp_1761_;
}
}
else
{
if (v___x_1841_ == 0)
{
v___y_1762_ = v___y_1833_;
v___y_1763_ = v___y_1837_;
v___y_1764_ = v___y_1835_;
v___y_1765_ = v___y_1836_;
v___y_1766_ = v___x_1838_;
v___y_1767_ = v___y_1834_;
v___y_1768_ = v___y_1832_;
goto v___jp_1761_;
}
else
{
v___y_1801_ = v___y_1832_;
v___y_1802_ = v___y_1833_;
v___y_1803_ = v___x_1760_;
v___y_1804_ = v___y_1837_;
v___y_1805_ = v___y_1834_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1836_;
v___y_1808_ = v___x_1838_;
goto v___jp_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___boxed(lean_object* v_stx_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Elab_Tactic_evalImpossible(v_stx_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_stx_2004_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___boxed(lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(lean_object* v_00_u03b1_2035_, lean_object* v_x_2036_, lean_object* v_mkInfoTree_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_2036_, v_mkInfoTree_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_x_2049_, lean_object* v_mkInfoTree_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(v_00_u03b1_2048_, v_x_2049_, v_mkInfoTree_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(lean_object* v_00_u03b1_2061_, lean_object* v_ref_2062_, lean_object* v_msg_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_2062_, v_msg_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_ref_2075_, lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(v_00_u03b1_2074_, v_ref_2075_, v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v_ref_2075_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(lean_object* v_00_u03b1_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_2088_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(v_00_u03b1_2099_, v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1(){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2125_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1));
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4));
v___x_2128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___boxed), 10, 0);
v___x_2129_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2125_, v___x_2126_, v___x_2127_, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___boxed(lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
return v_res_2131_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Impossible(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig = _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig);
res = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Impossible(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Impossible(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Impossible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Impossible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Impossible(builtin);
}
#ifdef __cplusplus
}
#endif
