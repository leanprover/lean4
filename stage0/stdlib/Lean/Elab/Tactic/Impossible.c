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
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
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
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__7;
static const lean_array_object l_Lean_Elab_Tactic_evalImpossible___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalImpossible___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_impossible"};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalImpossible___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__9_value),LEAN_SCALAR_PTR_LITERAL(88, 100, 77, 38, 182, 7, 158, 172)}};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_evalImpossible___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`impossible`: goal contains universe metavariables"};
static const lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalImpossible___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalImpossible___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalImpossible___closed__12;
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
lean_object* v_negBody_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___x_157_; 
lean_inc_ref(v_revBody_142_);
v___x_157_ = l_Lean_Meta_isProp(v_revBody_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1));
v___x_161_ = l_Lean_mkConst(v___x_160_, v___x_140_);
v___x_162_ = l_Lean_mkArrow(v_revBody_142_, v___x_161_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v_negBody_149_ = v_a_163_;
v___y_150_ = v___y_143_;
v___y_151_ = v___y_144_;
v___y_152_ = v___y_145_;
v___y_153_ = v___y_146_;
goto v___jp_148_;
}
else
{
return v___x_162_;
}
}
else
{
lean_object* v___x_164_; 
lean_dec(v___x_140_);
v___x_164_ = l_Lean_mkNot(v_revBody_142_);
v_negBody_149_ = v___x_164_;
v___y_150_ = v___y_143_;
v___y_151_ = v___y_144_;
v___y_152_ = v___y_145_;
v___y_153_ = v___y_146_;
goto v___jp_148_;
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec_ref(v_revBody_142_);
lean_dec(v___x_140_);
v_a_165_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_157_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_157_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
v___jp_148_:
{
uint8_t v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = 1;
v___x_155_ = 1;
v___x_156_ = l_Lean_Meta_mkForallFVars(v_ms_141_, v_negBody_149_, v___x_139_, v___x_154_, v___x_154_, v___x_155_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed(lean_object* v___x_173_, lean_object* v___x_174_, lean_object* v_ms_175_, lean_object* v_revBody_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v___x_3360__boxed_182_; lean_object* v_res_183_; 
v___x_3360__boxed_182_ = lean_unbox(v___x_173_);
v_res_183_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(v___x_3360__boxed_182_, v___x_174_, v_ms_175_, v_revBody_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v_ms_175_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(size_t v_sz_184_, size_t v_i_185_, lean_object* v_bs_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_usize_dec_lt(v_i_185_, v_sz_184_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v_bs_186_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_mkFreshLevelMVar(v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v_bs_x27_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = lean_unsigned_to_nat(0u);
v_bs_x27_197_ = lean_array_uset(v_bs_186_, v_i_185_, v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_185_, v___x_198_);
v___x_200_ = lean_array_uset(v_bs_x27_197_, v_i_185_, v_a_195_);
v_i_185_ = v___x_199_;
v_bs_186_ = v___x_200_;
goto _start;
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_bs_186_);
v_a_202_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_194_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_194_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2___boxed(lean_object* v_sz_210_, lean_object* v_i_211_, lean_object* v_bs_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
size_t v_sz_boxed_218_; size_t v_i_boxed_219_; lean_object* v_res_220_; 
v_sz_boxed_218_ = lean_unbox_usize(v_sz_210_);
lean_dec(v_sz_210_);
v_i_boxed_219_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_boxed_218_, v_i_boxed_219_, v_bs_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_bs_226_);
return v___x_233_;
}
else
{
lean_object* v_v_234_; lean_object* v___x_235_; lean_object* v_bs_x27_236_; lean_object* v_a_238_; 
v_v_234_ = lean_array_uget(v_bs_226_, v_i_225_);
v___x_235_ = lean_unsigned_to_nat(0u);
v_bs_x27_236_ = lean_array_uset(v_bs_226_, v_i_225_, v___x_235_);
if (lean_obj_tag(v_v_234_) == 2)
{
lean_object* v_mvarId_243_; lean_object* v___x_244_; 
v_mvarId_243_ = lean_ctor_get(v_v_234_, 0);
lean_inc(v_mvarId_243_);
lean_dec_ref_known(v_v_234_, 1);
v___x_244_ = l_Lean_MVarId_getDecl(v_mvarId_243_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_userName_246_; uint8_t v___x_247_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v_userName_246_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_userName_246_);
lean_dec(v_a_245_);
v___x_247_ = l_Lean_Name_isAnonymous(v_userName_246_);
if (v___x_247_ == 0)
{
v_a_238_ = v_userName_246_;
goto v___jp_237_;
}
else
{
lean_object* v___x_248_; 
lean_dec(v_userName_246_);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1));
v_a_238_ = v___x_248_;
goto v___jp_237_;
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v_bs_x27_236_);
v_a_249_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_244_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_244_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v___x_257_; 
lean_dec(v_v_234_);
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1));
v_a_238_ = v___x_257_;
goto v___jp_237_;
}
v___jp_237_:
{
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_225_, v___x_239_);
v___x_241_ = lean_array_uset(v_bs_x27_236_, v_i_225_, v_a_238_);
v_i_225_ = v___x_240_;
v_bs_226_ = v___x_241_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___boxed(lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_bs_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
size_t v_sz_boxed_266_; size_t v_i_boxed_267_; lean_object* v_res_268_; 
v_sz_boxed_266_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_267_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_boxed_266_, v_i_boxed_267_, v_bs_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_268_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_box(0);
v___x_273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1));
v___x_274_ = l_Lean_mkConst(v___x_273_, v___x_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(lean_object* v_goalType_279_, lean_object* v___x_280_, uint8_t v_cfg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_279_, v___x_280_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___x_289_ = l_Lean_Expr_mvarId_x21(v_a_288_);
lean_dec(v_a_288_);
v___x_290_ = l_Lean_MVarId_revertAll(v___x_289_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_MVarId_getType(v_a_291_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2);
v___x_295_ = 0;
v___x_296_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_a_293_, v___x_294_, v___x_295_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___f_298_; lean_object* v_rTypeLevels_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___f_298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3));
if (v_cfg_281_ == 0)
{
lean_object* v_levelArgs_341_; 
v_levelArgs_341_ = lean_ctor_get(v_a_297_, 3);
lean_inc_ref(v_levelArgs_341_);
v_rTypeLevels_300_ = v_levelArgs_341_;
v___y_301_ = v___y_282_;
v___y_302_ = v___y_283_;
v___y_303_ = v___y_284_;
v___y_304_ = v___y_285_;
goto v___jp_299_;
}
else
{
lean_object* v_levelParams_342_; size_t v_sz_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_levelParams_342_ = lean_ctor_get(v_a_297_, 0);
v_sz_343_ = lean_array_size(v_levelParams_342_);
v___x_344_ = ((size_t)0ULL);
lean_inc_ref(v_levelParams_342_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_343_, v___x_344_, v_levelParams_342_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_rTypeLevels_300_ = v_a_346_;
v___y_301_ = v___y_282_;
v___y_302_ = v___y_283_;
v___y_303_ = v___y_284_;
v___y_304_ = v___y_285_;
goto v___jp_299_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_297_);
v_a_347_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_345_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
v___jp_299_:
{
lean_object* v_levelParams_305_; lean_object* v_type_306_; lean_object* v_exprArgs_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_levelParams_305_ = lean_ctor_get(v_a_297_, 0);
lean_inc_ref(v_levelParams_305_);
v_type_306_ = lean_ctor_get(v_a_297_, 1);
lean_inc_ref(v_type_306_);
v_exprArgs_307_ = lean_ctor_get(v_a_297_, 4);
lean_inc_ref(v_exprArgs_307_);
lean_dec(v_a_297_);
v___x_308_ = l_Lean_Expr_instantiateLevelParamsArray(v_type_306_, v_levelParams_305_, v_rTypeLevels_300_);
lean_dec_ref(v_type_306_);
v___x_309_ = lean_array_get_size(v_exprArgs_307_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v___x_308_, v___x_310_, v___f_298_, v___x_295_, v___x_295_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; size_t v_sz_313_; size_t v___x_314_; lean_object* v___x_315_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v_sz_313_ = lean_array_size(v_exprArgs_307_);
v___x_314_ = ((size_t)0ULL);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_313_, v___x_314_, v_exprArgs_307_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_a_312_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_a_312_);
v_a_325_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_315_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_exprArgs_307_);
v_a_333_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_311_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_311_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_a_355_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_296_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_296_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_292_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_292_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_290_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_290_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_287_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_287_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed(lean_object* v_goalType_387_, lean_object* v___x_388_, lean_object* v_cfg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_cfg_boxed_395_; lean_object* v_res_396_; 
v_cfg_boxed_395_ = lean_unbox(v_cfg_389_);
v_res_396_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(v_goalType_387_, v___x_388_, v_cfg_boxed_395_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(lean_object* v_mainGoal_397_, lean_object* v_goalType_398_, uint8_t v_cfg_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_box(v_cfg_399_);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed), 8, 3);
lean_closure_set(v___f_407_, 0, v_goalType_398_);
lean_closure_set(v___f_407_, 1, v___x_405_);
lean_closure_set(v___f_407_, 2, v___x_406_);
v___x_408_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mainGoal_397_, v___f_407_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___boxed(lean_object* v_mainGoal_409_, lean_object* v_goalType_410_, lean_object* v_cfg_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_cfg_boxed_417_; lean_object* v_res_418_; 
v_cfg_boxed_417_ = lean_unbox(v_cfg_411_);
v_res_418_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(v_mainGoal_409_, v_goalType_410_, v_cfg_boxed_417_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_418_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(0);
v___x_420_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(lean_object* v_00_u03b1_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(v_00_u03b1_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(lean_object* v_msgData_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; lean_object* v_env_448_; lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_lctx_451_; lean_object* v_options_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_447_ = lean_st_ref_get(v___y_445_);
v_env_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_448_);
lean_dec(v___x_447_);
v___x_449_ = lean_st_ref_get(v___y_443_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_mctx_450_);
lean_dec(v___x_449_);
v_lctx_451_ = lean_ctor_get(v___y_442_, 2);
v_options_452_ = lean_ctor_get(v___y_444_, 1);
lean_inc_ref(v_options_452_);
lean_inc_ref(v_lctx_451_);
v___x_453_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_453_, 0, v_env_448_);
lean_ctor_set(v___x_453_, 1, v_mctx_450_);
lean_ctor_set(v___x_453_, 2, v_lctx_451_);
lean_ctor_set(v___x_453_, 3, v_options_452_);
v___x_454_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_msgData_441_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msgData_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_ref_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
v_ref_469_ = lean_ctor_get(v___y_466_, 4);
v___x_470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_inc(v_ref_469_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_ref_469_);
lean_ctor_set(v___x_475_, 1, v_a_471_);
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 1);
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(lean_object* v___x_491_, lean_object* v_ctor_492_, lean_object* v_args_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0));
v___x_520_ = lean_string_dec_eq(v_ctor_492_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_get_size(v_args_493_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2);
v___x_526_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v___x_525_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
goto v___jp_499_;
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get_borrowed(v___x_491_, v_args_493_, v___x_500_);
lean_inc(v___x_501_);
v___x_502_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_501_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
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
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_502_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_502_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(lean_object* v___x_535_, lean_object* v_ctor_536_, lean_object* v_args_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(v___x_535_, v_ctor_536_, v_args_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_args_537_);
lean_dec_ref(v_ctor_536_);
lean_dec_ref(v___x_535_);
return v_res_543_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_544_; lean_object* v___f_545_; 
v___x_544_ = l_Lean_instInhabitedExpr;
v___f_545_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_545_, 0, v___x_544_);
return v___f_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___f_561_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0);
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_563_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_562_, v___f_561_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed(lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(lean_object* v_00_u03b1_571_, lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(v_00_u03b1_579_, v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_590_ = l_Lean_Expr_const___override(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0));
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3);
return v___x_596_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(1);
v___x_598_ = l_Lean_MessageData_ofFormat(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_603_ = l_Lean_MessageData_ofFormat(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
return v_x_604_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_629_; 
v_head_606_ = lean_ctor_get(v_x_605_, 0);
v_tail_607_ = lean_ctor_get(v_x_605_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_629_ == 0)
{
v___x_609_ = v_x_605_;
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_tail_607_);
lean_inc(v_head_606_);
lean_dec(v_x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_before_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_627_; 
v_before_611_ = lean_ctor_get(v_head_606_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_head_606_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_head_606_, 1);
lean_dec(v_unused_628_);
v___x_613_ = v_head_606_;
v_isShared_614_ = v_isSharedCheck_627_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_before_611_);
lean_dec(v_head_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_627_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 7);
lean_ctor_set(v___x_613_, 1, v___x_615_);
lean_ctor_set(v___x_613_, 0, v_x_604_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_x_604_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_615_);
v___x_617_ = v_reuseFailAlloc_626_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 7);
lean_ctor_set(v___x_609_, 1, v___x_618_);
lean_ctor_set(v___x_609_, 0, v___x_617_);
v___x_620_ = v___x_609_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_625_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_MessageData_ofSyntax(v_before_611_);
v___x_622_ = l_Lean_indentD(v___x_621_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_620_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v_x_604_ = v___x_623_;
v_x_605_ = v_tail_607_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_630_, lean_object* v_opt_631_){
_start:
{
lean_object* v_name_632_; lean_object* v_defValue_633_; lean_object* v_map_634_; lean_object* v___x_635_; 
v_name_632_ = lean_ctor_get(v_opt_631_, 0);
v_defValue_633_ = lean_ctor_get(v_opt_631_, 1);
v_map_634_ = lean_ctor_get(v_opts_630_, 0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_634_, v_name_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = lean_unbox(v_defValue_633_);
return v___x_636_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_635_, 1);
if (lean_obj_tag(v_val_637_) == 1)
{
uint8_t v_v_638_; 
v_v_638_ = lean_ctor_get_uint8(v_val_637_, 0);
lean_dec_ref_known(v_val_637_, 0);
return v_v_638_;
}
else
{
uint8_t v___x_639_; 
lean_dec(v_val_637_);
v___x_639_ = lean_unbox(v_defValue_633_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_640_, lean_object* v_opt_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_640_, v_opt_641_);
lean_dec_ref(v_opt_641_);
lean_dec_ref(v_opts_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_648_ = l_Lean_MessageData_ofFormat(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_649_, lean_object* v_macroStack_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_options_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_options_653_ = lean_ctor_get(v___y_651_, 1);
v___x_654_ = l_Lean_Elab_pp_macroStack;
v___x_655_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_macroStack_650_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_msgData_649_);
return v___x_656_;
}
else
{
if (lean_obj_tag(v_macroStack_650_) == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_msgData_649_);
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_after_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_674_; 
v_head_658_ = lean_ctor_get(v_macroStack_650_, 0);
lean_inc(v_head_658_);
v_after_659_ = lean_ctor_get(v_head_658_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_head_658_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_head_658_, 0);
lean_dec(v_unused_675_);
v___x_661_ = v_head_658_;
v_isShared_662_ = v_isSharedCheck_674_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_after_659_);
lean_dec(v_head_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_674_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 7);
lean_ctor_set(v___x_661_, 1, v___x_663_);
lean_ctor_set(v___x_661_, 0, v_msgData_649_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_msgData_649_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_673_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_msgData_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_666_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_MessageData_ofSyntax(v_after_659_);
v___x_669_ = l_Lean_indentD(v___x_668_);
v_msgData_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_670_, 0, v___x_667_);
lean_ctor_set(v_msgData_670_, 1, v___x_669_);
v___x_671_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_670_, v_macroStack_650_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_676_, lean_object* v_macroStack_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_676_, v_macroStack_677_, v___y_678_);
lean_dec_ref(v___y_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_ref_689_; lean_object* v___x_690_; lean_object* v_a_691_; lean_object* v_macroStack_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_ref_689_ = lean_ctor_get(v___y_686_, 4);
v___x_690_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_681_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
v_macroStack_692_ = lean_ctor_get(v___y_682_, 1);
v___x_693_ = l_Lean_Elab_getBetterRef(v_ref_689_, v_macroStack_692_);
lean_inc(v_macroStack_692_);
v___x_694_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_691_, v_macroStack_692_, v___y_686_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_693_);
lean_ctor_set(v___x_699_, 1, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 1);
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_712_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_Elab_abortTermExceptionId;
v___x_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Expr_hasMVar(v_e_721_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_e_721_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v_mctx_727_; lean_object* v___x_728_; lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_731_; lean_object* v_cache_732_; lean_object* v_zetaDeltaFVarIds_733_; lean_object* v_postponed_734_; lean_object* v_diag_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_744_; 
v___x_726_ = lean_st_ref_get(v___y_722_);
v_mctx_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_mctx_727_);
lean_dec(v___x_726_);
v___x_728_ = l_Lean_instantiateMVarsCore(v_mctx_727_, v_e_721_);
v_fst_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_fst_729_);
v_snd_730_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_snd_730_);
lean_dec_ref(v___x_728_);
v___x_731_ = lean_st_ref_take(v___y_722_);
v_cache_732_ = lean_ctor_get(v___x_731_, 1);
v_zetaDeltaFVarIds_733_ = lean_ctor_get(v___x_731_, 2);
v_postponed_734_ = lean_ctor_get(v___x_731_, 3);
v_diag_735_ = lean_ctor_get(v___x_731_, 4);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_745_);
v___x_737_ = v___x_731_;
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_diag_735_);
lean_inc(v_postponed_734_);
lean_inc(v_zetaDeltaFVarIds_733_);
lean_inc(v_cache_732_);
lean_dec(v___x_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_snd_730_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_snd_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_cache_732_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_zetaDeltaFVarIds_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_postponed_734_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_diag_735_);
v___x_740_ = v_reuseFailAlloc_743_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_st_ref_put(v___y_722_, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_fst_729_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_746_, v___y_747_);
lean_dec(v___y_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
v___x_754_ = l_Lean_MessageData_ofExpr(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2);
v___x_756_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5);
v___x_762_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(lean_object* v_stx_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_ty_x3f_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_toCold_784_; lean_object* v_options_785_; lean_object* v_currRecDepth_786_; lean_object* v_maxRecDepth_787_; lean_object* v_ref_788_; lean_object* v_currNamespace_789_; lean_object* v_openDecls_790_; lean_object* v_initHeartbeats_791_; lean_object* v_maxHeartbeats_792_; lean_object* v_currMacroScope_793_; uint8_t v_diag_794_; uint8_t v_suppressElabErrors_795_; uint8_t v___x_796_; lean_object* v_ref_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_ty_x3f_778_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
v___x_779_ = 1;
v___x_780_ = lean_box(0);
v___x_781_ = lean_box(v___x_779_);
v___x_782_ = lean_box(v___x_779_);
lean_inc(v_stx_770_);
v___x_783_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_783_, 0, v_stx_770_);
lean_closure_set(v___x_783_, 1, v_ty_x3f_778_);
lean_closure_set(v___x_783_, 2, v___x_781_);
lean_closure_set(v___x_783_, 3, v___x_782_);
lean_closure_set(v___x_783_, 4, v___x_780_);
v_toCold_784_ = lean_ctor_get(v_a_775_, 0);
v_options_785_ = lean_ctor_get(v_a_775_, 1);
v_currRecDepth_786_ = lean_ctor_get(v_a_775_, 2);
v_maxRecDepth_787_ = lean_ctor_get(v_a_775_, 3);
v_ref_788_ = lean_ctor_get(v_a_775_, 4);
v_currNamespace_789_ = lean_ctor_get(v_a_775_, 5);
v_openDecls_790_ = lean_ctor_get(v_a_775_, 6);
v_initHeartbeats_791_ = lean_ctor_get(v_a_775_, 7);
v_maxHeartbeats_792_ = lean_ctor_get(v_a_775_, 8);
v_currMacroScope_793_ = lean_ctor_get(v_a_775_, 9);
v_diag_794_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*10);
v_suppressElabErrors_795_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*10 + 1);
v___x_796_ = 1;
v_ref_797_ = l_Lean_replaceRef(v_stx_770_, v_ref_788_);
lean_dec(v_stx_770_);
lean_inc(v_currMacroScope_793_);
lean_inc(v_maxHeartbeats_792_);
lean_inc(v_initHeartbeats_791_);
lean_inc(v_openDecls_790_);
lean_inc(v_currNamespace_789_);
lean_inc(v_maxRecDepth_787_);
lean_inc(v_currRecDepth_786_);
lean_inc_ref(v_options_785_);
lean_inc_ref(v_toCold_784_);
v___x_798_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_798_, 0, v_toCold_784_);
lean_ctor_set(v___x_798_, 1, v_options_785_);
lean_ctor_set(v___x_798_, 2, v_currRecDepth_786_);
lean_ctor_set(v___x_798_, 3, v_maxRecDepth_787_);
lean_ctor_set(v___x_798_, 4, v_ref_797_);
lean_ctor_set(v___x_798_, 5, v_currNamespace_789_);
lean_ctor_set(v___x_798_, 6, v_openDecls_790_);
lean_ctor_set(v___x_798_, 7, v_initHeartbeats_791_);
lean_ctor_set(v___x_798_, 8, v_maxHeartbeats_792_);
lean_ctor_set(v___x_798_, 9, v_currMacroScope_793_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*10, v_diag_794_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*10 + 1, v_suppressElabErrors_795_);
v___x_799_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_783_, v___x_796_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v___x_798_, v_a_776_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; uint8_t v___x_897_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_800_, v_a_774_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_897_ = l_Lean_Expr_hasSorry(v_a_802_);
if (v___x_897_ == 0)
{
v___y_842_ = v_a_771_;
v___y_843_ = v_a_772_;
v___y_844_ = v_a_773_;
v___y_845_ = v_a_774_;
v___y_846_ = v___x_798_;
v___y_847_ = v_a_776_;
goto v___jp_841_;
}
else
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_Expr_hasSyntheticSorry(v_a_802_);
if (v___x_898_ == 0)
{
v___y_879_ = v_a_771_;
v___y_880_ = v_a_772_;
v___y_881_ = v_a_773_;
v___y_882_ = v_a_774_;
v___y_883_ = v___x_798_;
v___y_884_ = v_a_776_;
goto v___jp_878_;
}
else
{
lean_object* v___x_899_; lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_802_);
lean_dec_ref_known(v___x_798_, 10);
v___x_899_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
v___jp_803_:
{
if (v___y_813_ == 0)
{
if (lean_obj_tag(v___y_808_) == 0)
{
lean_dec_ref_known(v___y_808_, 2);
lean_dec_ref(v___y_807_);
lean_dec(v_a_802_);
return v___y_809_;
}
else
{
lean_object* v_id_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_827_; 
v_id_814_ = lean_ctor_get(v___y_808_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___y_808_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___y_808_, 1);
lean_dec(v_unused_828_);
v___x_816_ = v___y_808_;
v_isShared_817_ = v_isSharedCheck_827_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_id_814_);
lean_dec(v___y_808_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_827_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_instBEqInternalExceptionId_beq(v___y_811_, v_id_814_);
lean_dec(v_id_814_);
if (v___x_818_ == 0)
{
lean_del_object(v___x_816_);
lean_dec_ref(v___y_807_);
lean_dec(v_a_802_);
return v___y_809_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec_ref(v___y_809_);
v___x_819_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6);
v___x_820_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8);
v___x_821_ = l_Lean_indentExpr(v_a_802_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 7);
lean_ctor_set(v___x_816_, 1, v___x_821_);
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_826_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_819_);
v___x_825_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_824_, v___y_804_, v___y_806_, v___y_812_, v___y_810_, v___y_807_, v___y_805_);
lean_dec_ref(v___y_807_);
return v___x_825_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_a_802_);
return v___y_809_;
}
}
v___jp_829_:
{
lean_object* v___x_836_; 
lean_inc(v_a_802_);
v___x_836_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_802_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_dec_ref(v___y_834_);
lean_dec(v_a_802_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
v___x_838_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_839_ = l_Lean_Exception_isInterrupt(v_a_837_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
lean_inc(v_a_837_);
v___x_840_ = l_Lean_Exception_isRuntime(v_a_837_);
v___y_804_ = v___y_830_;
v___y_805_ = v___y_835_;
v___y_806_ = v___y_831_;
v___y_807_ = v___y_834_;
v___y_808_ = v_a_837_;
v___y_809_ = v___x_836_;
v___y_810_ = v___y_833_;
v___y_811_ = v___x_838_;
v___y_812_ = v___y_832_;
v___y_813_ = v___x_840_;
goto v___jp_803_;
}
else
{
v___y_804_ = v___y_830_;
v___y_805_ = v___y_835_;
v___y_806_ = v___y_831_;
v___y_807_ = v___y_834_;
v___y_808_ = v_a_837_;
v___y_809_ = v___x_836_;
v___y_810_ = v___y_833_;
v___y_811_ = v___x_838_;
v___y_812_ = v___y_832_;
v___y_813_ = v___x_839_;
goto v___jp_803_;
}
}
}
v___jp_841_:
{
lean_object* v___x_848_; 
lean_inc(v_a_802_);
v___x_848_ = l_Lean_Meta_getMVars(v_a_802_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_849_, v___x_780_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v_a_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; uint8_t v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_unbox(v_a_851_);
lean_dec(v_a_851_);
if (v___x_852_ == 0)
{
v___y_830_ = v___y_842_;
v___y_831_ = v___y_843_;
v___y_832_ = v___y_844_;
v___y_833_ = v___y_845_;
v___y_834_ = v___y_846_;
v___y_835_ = v___y_847_;
goto v___jp_829_;
}
else
{
lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v___y_846_);
lean_dec(v_a_802_);
v___x_853_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___y_846_);
lean_dec(v_a_802_);
v_a_862_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_850_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_850_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v___y_846_);
lean_dec(v_a_802_);
v_a_870_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_848_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_848_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
v___jp_878_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v___x_885_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10);
v___x_886_ = l_Lean_indentExpr(v_a_802_);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_887_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec_ref(v___y_883_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref_known(v___x_798_, 10);
v_a_908_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_799_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_799_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_stx_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(uint8_t v_config_935_, lean_object* v_item_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_item_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_955_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_936_, v___x_954_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_955_) == 0)
{
uint8_t v___x_956_; 
lean_dec_ref_known(v___x_955_, 1);
v___x_956_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_936_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_957_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_936_);
lean_inc_ref(v_item_936_);
v___x_958_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_936_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1));
v___x_960_ = lean_string_dec_eq(v___x_957_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2));
v___x_962_ = lean_string_dec_eq(v___x_957_, v___x_961_);
lean_dec_ref(v___x_957_);
if (v___x_962_ == 0)
{
lean_dec_ref(v_item_936_);
v_item_945_ = v___x_958_;
v___y_946_ = v___y_937_;
v___y_947_ = v___y_938_;
v___y_948_ = v___y_939_;
v___y_949_ = v___y_940_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
goto v___jp_944_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3));
v___x_964_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_936_, v___x_963_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_964_) == 0)
{
uint8_t v___x_965_; 
lean_dec_ref_known(v___x_964_, 1);
v___x_965_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_958_);
if (v___x_965_ == 0)
{
lean_dec_ref(v_item_936_);
v_item_945_ = v___x_958_;
v___y_946_ = v___y_937_;
v___y_947_ = v___y_938_;
v___y_948_ = v___y_939_;
v___y_949_ = v___y_940_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
goto v___jp_944_;
}
else
{
lean_object* v___x_966_; 
lean_dec_ref(v___x_958_);
v___x_966_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_a_975_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_966_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_966_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v___x_958_);
lean_dec_ref(v_item_936_);
v_a_983_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_964_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_964_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
else
{
uint8_t v___x_991_; 
lean_dec_ref(v___x_957_);
v___x_991_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_958_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_item_936_);
v_item_945_ = v___x_958_;
v___y_946_ = v___y_937_;
v___y_947_ = v___y_938_;
v___y_948_ = v___y_939_;
v___y_949_ = v___y_940_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
goto v___jp_944_;
}
else
{
lean_object* v_value_992_; lean_object* v___x_993_; 
lean_dec_ref(v___x_958_);
v_value_992_ = lean_ctor_get(v_item_936_, 2);
lean_inc(v_value_992_);
lean_dec_ref(v_item_936_);
v___x_993_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_value_992_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v___x_993_;
}
}
}
else
{
v_item_945_ = v_item_936_;
v___y_946_ = v___y_937_;
v___y_947_ = v___y_938_;
v___y_948_ = v___y_939_;
v___y_949_ = v___y_940_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
goto v___jp_944_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v_item_936_);
v_a_994_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_955_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_955_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
v___jp_944_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0));
v___x_953_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_945_, v___x_952_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1002_, lean_object* v_item_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_config_3650__boxed_1011_; lean_object* v_res_1012_; 
v_config_3650__boxed_1011_ = lean_unbox(v_config_1002_);
v_res_1012_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(v_config_3650__boxed_1011_, v_item_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1015_, v___y_1019_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(v_e_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1051_, lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_msg_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1061_, v_msg_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1071_, lean_object* v_macroStack_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1071_, v_macroStack_1072_, v___y_1077_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1081_, lean_object* v_macroStack_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1081_, v_macroStack_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_1093_ = l_Lean_mkConst(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(uint8_t v_cfg_1096_, lean_object* v_cfgItem_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1);
v___x_1106_ = lean_box(v_cfg_1096_);
v___x_1107_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_1106_, v_cfgItem_1097_, v___x_1105_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed(lean_object* v_cfg_1108_, lean_object* v_cfgItem_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v_cfg_boxed_1117_; lean_object* v_res_1118_; 
v_cfg_boxed_1117_ = lean_unbox(v_cfg_1108_);
v_res_1118_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(v_cfg_boxed_1117_, v_cfgItem_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v_cfgItem_1109_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(lean_object* v_cfg_1120_, uint8_t v_init_1121_, uint8_t v_logExceptions_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_onErr_1127_; lean_object* v_eval_1128_; 
v_onErr_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0));
v_eval_1128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0));
if (v_logExceptions_1122_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_box(v_init_1121_);
v___x_1130_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1128_, v___x_1129_, v_cfg_1120_, v_onErr_1127_, v_logExceptions_1122_, v_a_1124_, v_a_1125_);
return v___x_1130_;
}
else
{
uint8_t v_recover_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_recover_1131_ = lean_ctor_get_uint8(v_a_1123_, sizeof(void*)*1);
v___x_1132_ = lean_box(v_init_1121_);
v___x_1133_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1128_, v___x_1132_, v_cfg_1120_, v_onErr_1127_, v_recover_1131_, v_a_1124_, v_a_1125_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___boxed(lean_object* v_cfg_1134_, lean_object* v_init_1135_, lean_object* v_logExceptions_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
uint8_t v_init_boxed_1141_; uint8_t v_logExceptions_boxed_1142_; lean_object* v_res_1143_; 
v_init_boxed_1141_ = lean_unbox(v_init_1135_);
v_logExceptions_boxed_1142_ = lean_unbox(v_logExceptions_1136_);
v_res_1143_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1134_, v_init_boxed_1141_, v_logExceptions_boxed_1142_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig(lean_object* v_cfg_1144_, uint8_t v_init_1145_, uint8_t v_logExceptions_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1144_, v_init_1145_, v_logExceptions_1146_, v_a_1147_, v_a_1153_, v_a_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___boxed(lean_object* v_cfg_1157_, lean_object* v_init_1158_, lean_object* v_logExceptions_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_init_boxed_1169_; uint8_t v_logExceptions_boxed_1170_; lean_object* v_res_1171_; 
v_init_boxed_1169_ = lean_unbox(v_init_1158_);
v_logExceptions_boxed_1170_ = lean_unbox(v_logExceptions_1159_);
v_res_1171_ = l_Lean_Elab_Tactic_elabImpossibleConfig(v_cfg_1157_, v_init_boxed_1169_, v_logExceptions_boxed_1170_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(lean_object* v_e_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Lean_Expr_hasMVar(v_e_1172_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_e_1172_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v_mctx_1178_; lean_object* v___x_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; lean_object* v_cache_1183_; lean_object* v_zetaDeltaFVarIds_1184_; lean_object* v_postponed_1185_; lean_object* v_diag_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
v___x_1177_ = lean_st_ref_get(v___y_1173_);
v_mctx_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_ref(v_mctx_1178_);
lean_dec(v___x_1177_);
v___x_1179_ = l_Lean_instantiateMVarsCore(v_mctx_1178_, v_e_1172_);
v_fst_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_fst_1180_);
v_snd_1181_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_snd_1181_);
lean_dec_ref(v___x_1179_);
v___x_1182_ = lean_st_ref_take(v___y_1173_);
v_cache_1183_ = lean_ctor_get(v___x_1182_, 1);
v_zetaDeltaFVarIds_1184_ = lean_ctor_get(v___x_1182_, 2);
v_postponed_1185_ = lean_ctor_get(v___x_1182_, 3);
v_diag_1186_ = lean_ctor_get(v___x_1182_, 4);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1182_, 0);
lean_dec(v_unused_1196_);
v___x_1188_ = v___x_1182_;
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_diag_1186_);
lean_inc(v_postponed_1185_);
lean_inc(v_zetaDeltaFVarIds_1184_);
lean_inc(v_cache_1183_);
lean_dec(v___x_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_snd_1181_);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_snd_1181_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_cache_1183_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_zetaDeltaFVarIds_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_postponed_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_diag_1186_);
v___x_1191_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_st_ref_put(v___y_1173_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_fst_1180_);
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg___boxed(lean_object* v_e_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1197_, v___y_1198_);
lean_dec(v___y_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(lean_object* v_e_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1201_, v___y_1207_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___boxed(lean_object* v_e_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(v_e_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1233_ = lean_apply_9(v_x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, lean_box(0));
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed(lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(v_x_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(lean_object* v_mvarId_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___f_1256_; lean_object* v___x_1257_; 
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1256_, 0, v_x_1246_);
lean_closure_set(v___f_1256_, 1, v___y_1247_);
lean_closure_set(v___f_1256_, 2, v___y_1248_);
lean_closure_set(v___f_1256_, 3, v___y_1249_);
lean_closure_set(v___f_1256_, 4, v___y_1250_);
v___x_1257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1245_, v___f_1256_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1257_) == 0)
{
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___boxed(lean_object* v_mvarId_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1266_, v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(lean_object* v_00_u03b1_1278_, lean_object* v_mvarId_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1279_, v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_mvarId_1292_, lean_object* v_x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(v_00_u03b1_1291_, v_mvarId_1292_, v_x_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(lean_object* v_kind_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v_auxDeclNGen_1308_; lean_object* v___x_1309_; lean_object* v_env_1310_; lean_object* v___x_1311_; lean_object* v_fst_1312_; lean_object* v_snd_1313_; lean_object* v___x_1314_; lean_object* v_env_1315_; lean_object* v_nextMacroScope_1316_; lean_object* v_ngen_1317_; lean_object* v_traceState_1318_; lean_object* v_cache_1319_; lean_object* v_messages_1320_; lean_object* v_infoState_1321_; lean_object* v_snapshotTasks_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1331_; 
v___x_1307_ = lean_st_ref_get(v___y_1305_);
v_auxDeclNGen_1308_ = lean_ctor_get(v___x_1307_, 3);
lean_inc_ref(v_auxDeclNGen_1308_);
lean_dec(v___x_1307_);
v___x_1309_ = lean_st_ref_get(v___y_1305_);
v_env_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc_ref(v_env_1310_);
lean_dec(v___x_1309_);
v___x_1311_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_1310_, v_auxDeclNGen_1308_, v_kind_1304_);
v_fst_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_fst_1312_);
v_snd_1313_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_snd_1313_);
lean_dec_ref(v___x_1311_);
v___x_1314_ = lean_st_ref_take(v___y_1305_);
v_env_1315_ = lean_ctor_get(v___x_1314_, 0);
v_nextMacroScope_1316_ = lean_ctor_get(v___x_1314_, 1);
v_ngen_1317_ = lean_ctor_get(v___x_1314_, 2);
v_traceState_1318_ = lean_ctor_get(v___x_1314_, 4);
v_cache_1319_ = lean_ctor_get(v___x_1314_, 5);
v_messages_1320_ = lean_ctor_get(v___x_1314_, 6);
v_infoState_1321_ = lean_ctor_get(v___x_1314_, 7);
v_snapshotTasks_1322_ = lean_ctor_get(v___x_1314_, 8);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1314_, 3);
lean_dec(v_unused_1332_);
v___x_1324_ = v___x_1314_;
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snapshotTasks_1322_);
lean_inc(v_infoState_1321_);
lean_inc(v_messages_1320_);
lean_inc(v_cache_1319_);
lean_inc(v_traceState_1318_);
lean_inc(v_ngen_1317_);
lean_inc(v_nextMacroScope_1316_);
lean_inc(v_env_1315_);
lean_dec(v___x_1314_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 3, v_snd_1313_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_env_1315_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_nextMacroScope_1316_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_ngen_1317_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_snd_1313_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_traceState_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 5, v_cache_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 6, v_messages_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 7, v_infoState_1321_);
lean_ctor_set(v_reuseFailAlloc_1330_, 8, v_snapshotTasks_1322_);
v___x_1327_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_st_ref_put(v___y_1305_, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_fst_1312_);
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg___boxed(lean_object* v_kind_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1333_, v___y_1334_);
lean_dec(v___y_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(lean_object* v_kind_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1337_, v___y_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___boxed(lean_object* v_kind_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(v_kind_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(lean_object* v_opts_1359_, lean_object* v_opt_1360_){
_start:
{
lean_object* v_name_1361_; lean_object* v_defValue_1362_; lean_object* v_map_1363_; lean_object* v___x_1364_; 
v_name_1361_ = lean_ctor_get(v_opt_1360_, 0);
v_defValue_1362_ = lean_ctor_get(v_opt_1360_, 1);
v_map_1363_ = lean_ctor_get(v_opts_1359_, 0);
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1363_, v_name_1361_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_inc(v_defValue_1362_);
return v_defValue_1362_;
}
else
{
lean_object* v_val_1365_; 
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1364_, 1);
if (lean_obj_tag(v_val_1365_) == 3)
{
lean_object* v_v_1366_; 
v_v_1366_ = lean_ctor_get(v_val_1365_, 0);
lean_inc(v_v_1366_);
lean_dec_ref_known(v_val_1365_, 1);
return v_v_1366_;
}
else
{
lean_dec(v_val_1365_);
lean_inc(v_defValue_1362_);
return v_defValue_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(lean_object* v_opts_1367_, lean_object* v_opt_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v_opts_1367_, v_opt_1368_);
lean_dec_ref(v_opt_1368_);
lean_dec_ref(v_opts_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0(lean_object* v_a_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_MVarId_getType(v_a_1370_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_a_1381_, v___y_1376_);
return v___x_1382_;
}
else
{
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(lean_object* v_a_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Elab_Tactic_evalImpossible___lam__0(v_a_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1(lean_object* v___x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Elab_Tactic_evalTactic(v___x_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref_known(v___x_1404_, 1);
v___x_1405_ = l_Lean_Elab_Tactic_done(v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v___x_1405_;
}
else
{
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(lean_object* v___x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Elab_Tactic_evalImpossible___lam__1(v___x_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2(lean_object* v_a_1417_, lean_object* v_trees_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
v___x_1428_ = lean_apply_9(v_a_1417_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, lean_box(0));
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_a_1429_);
lean_ctor_set(v___x_1433_, 1, v_trees_1418_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_trees_1418_);
v_a_1438_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1428_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1428_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed(lean_object* v_a_1446_, lean_object* v_trees_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Elab_Tactic_evalImpossible___lam__2(v_a_1446_, v_trees_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1457_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_unsigned_to_nat(32u);
v___x_1459_ = lean_mk_empty_array_with_capacity(v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = ((size_t)5ULL);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_unsigned_to_nat(32u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0);
v___x_1466_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___x_1464_);
lean_ctor_set(v___x_1466_, 2, v___x_1462_);
lean_ctor_set(v___x_1466_, 3, v___x_1462_);
lean_ctor_set_usize(v___x_1466_, 4, v___x_1461_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_infoState_1470_; lean_object* v_trees_1471_; lean_object* v___x_1472_; lean_object* v_infoState_1473_; lean_object* v_env_1474_; lean_object* v_nextMacroScope_1475_; lean_object* v_ngen_1476_; lean_object* v_auxDeclNGen_1477_; lean_object* v_traceState_1478_; lean_object* v_cache_1479_; lean_object* v_messages_1480_; lean_object* v_snapshotTasks_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1502_; 
v___x_1469_ = lean_st_ref_get(v___y_1467_);
v_infoState_1470_ = lean_ctor_get(v___x_1469_, 7);
lean_inc_ref(v_infoState_1470_);
lean_dec(v___x_1469_);
v_trees_1471_ = lean_ctor_get(v_infoState_1470_, 2);
lean_inc_ref(v_trees_1471_);
lean_dec_ref(v_infoState_1470_);
v___x_1472_ = lean_st_ref_take(v___y_1467_);
v_infoState_1473_ = lean_ctor_get(v___x_1472_, 7);
v_env_1474_ = lean_ctor_get(v___x_1472_, 0);
v_nextMacroScope_1475_ = lean_ctor_get(v___x_1472_, 1);
v_ngen_1476_ = lean_ctor_get(v___x_1472_, 2);
v_auxDeclNGen_1477_ = lean_ctor_get(v___x_1472_, 3);
v_traceState_1478_ = lean_ctor_get(v___x_1472_, 4);
v_cache_1479_ = lean_ctor_get(v___x_1472_, 5);
v_messages_1480_ = lean_ctor_get(v___x_1472_, 6);
v_snapshotTasks_1481_ = lean_ctor_get(v___x_1472_, 8);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1483_ = v___x_1472_;
v_isShared_1484_ = v_isSharedCheck_1502_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snapshotTasks_1481_);
lean_inc(v_infoState_1473_);
lean_inc(v_messages_1480_);
lean_inc(v_cache_1479_);
lean_inc(v_traceState_1478_);
lean_inc(v_auxDeclNGen_1477_);
lean_inc(v_ngen_1476_);
lean_inc(v_nextMacroScope_1475_);
lean_inc(v_env_1474_);
lean_dec(v___x_1472_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1502_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint8_t v_enabled_1485_; lean_object* v_assignment_1486_; lean_object* v_lazyAssignment_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1500_; 
v_enabled_1485_ = lean_ctor_get_uint8(v_infoState_1473_, sizeof(void*)*3);
v_assignment_1486_ = lean_ctor_get(v_infoState_1473_, 0);
v_lazyAssignment_1487_ = lean_ctor_get(v_infoState_1473_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_infoState_1473_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_infoState_1473_, 2);
lean_dec(v_unused_1501_);
v___x_1489_ = v_infoState_1473_;
v_isShared_1490_ = v_isSharedCheck_1500_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_lazyAssignment_1487_);
lean_inc(v_assignment_1486_);
lean_dec(v_infoState_1473_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1500_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 2, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_assignment_1486_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_lazyAssignment_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v___x_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*3, v_enabled_1485_);
v___x_1493_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 7, v___x_1493_);
v___x_1495_ = v___x_1483_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_env_1474_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_nextMacroScope_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_ngen_1476_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_auxDeclNGen_1477_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_traceState_1478_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_cache_1479_);
lean_ctor_set(v_reuseFailAlloc_1498_, 6, v_messages_1480_);
lean_ctor_set(v_reuseFailAlloc_1498_, 7, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1498_, 8, v_snapshotTasks_1481_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_st_ref_put(v___y_1467_, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_trees_1471_);
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___boxed(lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1503_);
lean_dec(v___y_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(lean_object* v___y_1506_, lean_object* v_mkInfoTree_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v_a_1515_, lean_object* v_a_x3f_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v_infoState_1519_; lean_object* v_trees_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_st_ref_get(v___y_1506_);
v_infoState_1519_ = lean_ctor_get(v___x_1518_, 7);
lean_inc_ref(v_infoState_1519_);
lean_dec(v___x_1518_);
v_trees_1520_ = lean_ctor_get(v_infoState_1519_, 2);
lean_inc_ref(v_trees_1520_);
lean_dec_ref(v_infoState_1519_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1510_);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
v___x_1521_ = lean_apply_10(v_mkInfoTree_1507_, v_trees_1520_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1560_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1560_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1560_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v_infoState_1527_; lean_object* v_env_1528_; lean_object* v_nextMacroScope_1529_; lean_object* v_ngen_1530_; lean_object* v_auxDeclNGen_1531_; lean_object* v_traceState_1532_; lean_object* v_cache_1533_; lean_object* v_messages_1534_; lean_object* v_snapshotTasks_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1559_; 
v___x_1526_ = lean_st_ref_take(v___y_1506_);
v_infoState_1527_ = lean_ctor_get(v___x_1526_, 7);
v_env_1528_ = lean_ctor_get(v___x_1526_, 0);
v_nextMacroScope_1529_ = lean_ctor_get(v___x_1526_, 1);
v_ngen_1530_ = lean_ctor_get(v___x_1526_, 2);
v_auxDeclNGen_1531_ = lean_ctor_get(v___x_1526_, 3);
v_traceState_1532_ = lean_ctor_get(v___x_1526_, 4);
v_cache_1533_ = lean_ctor_get(v___x_1526_, 5);
v_messages_1534_ = lean_ctor_get(v___x_1526_, 6);
v_snapshotTasks_1535_ = lean_ctor_get(v___x_1526_, 8);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1537_ = v___x_1526_;
v_isShared_1538_ = v_isSharedCheck_1559_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snapshotTasks_1535_);
lean_inc(v_infoState_1527_);
lean_inc(v_messages_1534_);
lean_inc(v_cache_1533_);
lean_inc(v_traceState_1532_);
lean_inc(v_auxDeclNGen_1531_);
lean_inc(v_ngen_1530_);
lean_inc(v_nextMacroScope_1529_);
lean_inc(v_env_1528_);
lean_dec(v___x_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1559_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint8_t v_enabled_1539_; lean_object* v_assignment_1540_; lean_object* v_lazyAssignment_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1557_; 
v_enabled_1539_ = lean_ctor_get_uint8(v_infoState_1527_, sizeof(void*)*3);
v_assignment_1540_ = lean_ctor_get(v_infoState_1527_, 0);
v_lazyAssignment_1541_ = lean_ctor_get(v_infoState_1527_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_infoState_1527_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_infoState_1527_, 2);
lean_dec(v_unused_1558_);
v___x_1543_ = v_infoState_1527_;
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_lazyAssignment_1541_);
lean_inc(v_assignment_1540_);
lean_dec(v_infoState_1527_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = l_Lean_PersistentArray_push___redArg(v_a_1515_, v_a_1522_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 2, v___x_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_assignment_1540_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_lazyAssignment_1541_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v___x_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1556_, sizeof(void*)*3, v_enabled_1539_);
v___x_1547_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 7, v___x_1547_);
v___x_1549_ = v___x_1537_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_env_1528_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_nextMacroScope_1529_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_ngen_1530_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_auxDeclNGen_1531_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_traceState_1532_);
lean_ctor_set(v_reuseFailAlloc_1555_, 5, v_cache_1533_);
lean_ctor_set(v_reuseFailAlloc_1555_, 6, v_messages_1534_);
lean_ctor_set(v_reuseFailAlloc_1555_, 7, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1555_, 8, v_snapshotTasks_1535_);
v___x_1549_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1550_ = lean_st_ref_put(v___y_1506_, v___x_1549_);
v___x_1551_ = lean_box(0);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1551_);
v___x_1553_ = v___x_1524_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_a_1515_);
v_a_1561_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1521_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1521_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0___boxed(lean_object* v___y_1569_, lean_object* v_mkInfoTree_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v_a_1578_, lean_object* v_a_x3f_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1569_, v_mkInfoTree_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v_a_1578_, v_a_x3f_1579_);
lean_dec(v_a_x3f_1579_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1569_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(lean_object* v_x_1582_, lean_object* v_mkInfoTree_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_infoState_1594_; uint8_t v_enabled_1595_; 
v___x_1593_ = lean_st_ref_get(v___y_1591_);
v_infoState_1594_ = lean_ctor_get(v___x_1593_, 7);
lean_inc_ref(v_infoState_1594_);
lean_dec(v___x_1593_);
v_enabled_1595_ = lean_ctor_get_uint8(v_infoState_1594_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1594_);
if (v_enabled_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v_mkInfoTree_1583_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
v___x_1596_ = lean_apply_9(v_x_1582_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, lean_box(0));
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v_r_1599_; 
v___x_1597_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1591_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
v_r_1599_ = lean_apply_9(v_x_1582_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, lean_box(0));
if (lean_obj_tag(v_r_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1624_; 
v_a_1600_ = lean_ctor_get(v_r_1599_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_r_1599_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1602_ = v_r_1599_;
v_isShared_1603_ = v_isSharedCheck_1624_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_r_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1624_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
lean_inc(v_a_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 1);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1591_, v_mkInfoTree_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v_a_1598_, v___x_1605_);
lean_dec_ref(v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1614_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_a_1600_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1600_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1600_);
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1606_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1606_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1625_ = lean_ctor_get(v_r_1599_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v_r_1599_, 1);
v___x_1626_ = lean_box(0);
v___x_1627_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1591_, v_mkInfoTree_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v_a_1598_, v___x_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1635_);
v___x_1629_ = v___x_1627_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v___x_1627_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 1);
lean_ctor_set(v___x_1629_, 0, v_a_1625_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1625_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1625_);
v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1627_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1627_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___boxed(lean_object* v_x_1644_, lean_object* v_mkInfoTree_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_1644_, v_mkInfoTree_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(lean_object* v_o_1659_, lean_object* v_k_1660_, uint8_t v_v_1661_){
_start:
{
lean_object* v_map_1662_; uint8_t v_hasTrace_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1677_; 
v_map_1662_ = lean_ctor_get(v_o_1659_, 0);
v_hasTrace_1663_ = lean_ctor_get_uint8(v_o_1659_, sizeof(void*)*1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_o_1659_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1665_ = v_o_1659_;
v_isShared_1666_ = v_isSharedCheck_1677_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_map_1662_);
lean_dec(v_o_1659_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1677_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1667_, 0, v_v_1661_);
lean_inc(v_k_1660_);
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1660_, v___x_1667_, v_map_1662_);
if (v_hasTrace_1663_ == 0)
{
lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1672_; 
v___x_1669_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1));
v___x_1670_ = l_Lean_Name_isPrefixOf(v___x_1669_, v_k_1660_);
lean_dec(v_k_1660_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1668_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*1, v___x_1670_);
return v___x_1672_;
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_k_1660_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1675_ = v___x_1665_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*1, v_hasTrace_1663_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___boxed(lean_object* v_o_1678_, lean_object* v_k_1679_, lean_object* v_v_1680_){
_start:
{
uint8_t v_v_boxed_1681_; lean_object* v_res_1682_; 
v_v_boxed_1681_ = lean_unbox(v_v_1680_);
v_res_1682_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_o_1678_, v_k_1679_, v_v_boxed_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(lean_object* v_opts_1683_, lean_object* v_opt_1684_, uint8_t v_val_1685_){
_start:
{
lean_object* v_name_1686_; lean_object* v___x_1687_; 
v_name_1686_ = lean_ctor_get(v_opt_1684_, 0);
lean_inc(v_name_1686_);
lean_dec_ref(v_opt_1684_);
v___x_1687_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_opts_1683_, v_name_1686_, v_val_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(lean_object* v_opts_1688_, lean_object* v_opt_1689_, lean_object* v_val_1690_){
_start:
{
uint8_t v_val_boxed_1691_; lean_object* v_res_1692_; 
v_val_boxed_1691_ = lean_unbox(v_val_1690_);
v_res_1692_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v_opts_1688_, v_opt_1689_, v_val_boxed_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_ref_1699_; lean_object* v___x_1700_; lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1709_; 
v_ref_1699_ = lean_ctor_get(v___y_1696_, 4);
v___x_1700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_inc(v_ref_1699_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_ref_1699_);
lean_ctor_set(v___x_1705_, 1, v_a_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(lean_object* v_ref_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_toCold_1728_; lean_object* v_options_1729_; lean_object* v_currRecDepth_1730_; lean_object* v_maxRecDepth_1731_; lean_object* v_ref_1732_; lean_object* v_currNamespace_1733_; lean_object* v_openDecls_1734_; lean_object* v_initHeartbeats_1735_; lean_object* v_maxHeartbeats_1736_; lean_object* v_currMacroScope_1737_; uint8_t v_diag_1738_; uint8_t v_suppressElabErrors_1739_; lean_object* v_ref_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_toCold_1728_ = lean_ctor_get(v___y_1725_, 0);
v_options_1729_ = lean_ctor_get(v___y_1725_, 1);
v_currRecDepth_1730_ = lean_ctor_get(v___y_1725_, 2);
v_maxRecDepth_1731_ = lean_ctor_get(v___y_1725_, 3);
v_ref_1732_ = lean_ctor_get(v___y_1725_, 4);
v_currNamespace_1733_ = lean_ctor_get(v___y_1725_, 5);
v_openDecls_1734_ = lean_ctor_get(v___y_1725_, 6);
v_initHeartbeats_1735_ = lean_ctor_get(v___y_1725_, 7);
v_maxHeartbeats_1736_ = lean_ctor_get(v___y_1725_, 8);
v_currMacroScope_1737_ = lean_ctor_get(v___y_1725_, 9);
v_diag_1738_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*10);
v_suppressElabErrors_1739_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*10 + 1);
v_ref_1740_ = l_Lean_replaceRef(v_ref_1717_, v_ref_1732_);
lean_inc(v_currMacroScope_1737_);
lean_inc(v_maxHeartbeats_1736_);
lean_inc(v_initHeartbeats_1735_);
lean_inc(v_openDecls_1734_);
lean_inc(v_currNamespace_1733_);
lean_inc(v_maxRecDepth_1731_);
lean_inc(v_currRecDepth_1730_);
lean_inc_ref(v_options_1729_);
lean_inc_ref(v_toCold_1728_);
v___x_1741_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1741_, 0, v_toCold_1728_);
lean_ctor_set(v___x_1741_, 1, v_options_1729_);
lean_ctor_set(v___x_1741_, 2, v_currRecDepth_1730_);
lean_ctor_set(v___x_1741_, 3, v_maxRecDepth_1731_);
lean_ctor_set(v___x_1741_, 4, v_ref_1740_);
lean_ctor_set(v___x_1741_, 5, v_currNamespace_1733_);
lean_ctor_set(v___x_1741_, 6, v_openDecls_1734_);
lean_ctor_set(v___x_1741_, 7, v_initHeartbeats_1735_);
lean_ctor_set(v___x_1741_, 8, v_maxHeartbeats_1736_);
lean_ctor_set(v___x_1741_, 9, v_currMacroScope_1737_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*10, v_diag_1738_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*10 + 1, v_suppressElabErrors_1739_);
v___x_1742_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1718_, v___y_1723_, v___y_1724_, v___x_1741_, v___y_1726_);
lean_dec_ref_known(v___x_1741_, 10);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg___boxed(lean_object* v_ref_1743_, lean_object* v_msg_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_1743_, v_msg_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v_ref_1743_);
return v_res_1754_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__0(void){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__1(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__0, &l_Lean_Elab_Tactic_evalImpossible___closed__0_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__0);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__2(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__1, &l_Lean_Elab_Tactic_evalImpossible___closed__1_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__1);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__3(void){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__4(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__3, &l_Lean_Elab_Tactic_evalImpossible___closed__3_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__3);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__5(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_unsigned_to_nat(32u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__6(void){
_start:
{
size_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1766_ = ((size_t)5ULL);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_unsigned_to_nat(32u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__5, &l_Lean_Elab_Tactic_evalImpossible___closed__5_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__5);
v___x_1771_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
lean_ctor_set(v___x_1771_, 2, v___x_1767_);
lean_ctor_set(v___x_1771_, 3, v___x_1767_);
lean_ctor_set_usize(v___x_1771_, 4, v___x_1766_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__7(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = lean_box(1);
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__6, &l_Lean_Elab_Tactic_evalImpossible___closed__6_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__6);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__4, &l_Lean_Elab_Tactic_evalImpossible___closed__4_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__4);
v___x_1775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v___x_1773_);
lean_ctor_set(v___x_1775_, 2, v___x_1772_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__12(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__11));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible(lean_object* v_stx_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v_a_1797_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; lean_object* v_toCold_1831_; lean_object* v_currRecDepth_1832_; lean_object* v_ref_1833_; lean_object* v_currNamespace_1834_; lean_object* v_openDecls_1835_; lean_object* v_initHeartbeats_1836_; lean_object* v_maxHeartbeats_1837_; lean_object* v_currMacroScope_1838_; uint8_t v_suppressElabErrors_1839_; lean_object* v___y_1840_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; uint8_t v___y_1870_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = l_Lean_Syntax_getArg(v_stx_1784_, v___x_1822_);
v___x_1824_ = 0;
v___x_1891_ = 1;
v___x_1892_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v___x_1823_, v___x_1824_, v___x_1891_, v_a_1785_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1786_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_n(v_a_1895_, 3);
lean_dec_ref_known(v___x_1894_, 1);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1896_, 0, v_a_1895_);
v___x_1897_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_a_1895_, v___f_1896_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___f_1904_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; uint8_t v___x_2030_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_unsigned_to_nat(2u);
v___x_1901_ = l_Lean_Syntax_getArg(v_stx_1784_, v___x_1900_);
v___x_1902_ = lean_unsigned_to_nat(3u);
v___x_1903_ = l_Lean_Syntax_getArg(v_stx_1784_, v___x_1902_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1904_, 0, v___x_1903_);
v___x_2030_ = l_Lean_Expr_hasLevelMVar(v_a_1898_);
if (v___x_2030_ == 0)
{
v___y_1906_ = v_a_1785_;
v___y_1907_ = v_a_1786_;
v___y_1908_ = v_a_1787_;
v___y_1909_ = v_a_1788_;
v___y_1910_ = v_a_1789_;
v___y_1911_ = v_a_1790_;
v___y_1912_ = v_a_1791_;
v___y_1913_ = v_a_1792_;
goto v___jp_1905_;
}
else
{
lean_object* v_kw_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
lean_dec(v_a_1895_);
lean_dec(v_a_1893_);
v_kw_2031_ = l_Lean_Syntax_getArg(v_stx_1784_, v___x_1899_);
v___x_2032_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__12, &l_Lean_Elab_Tactic_evalImpossible___closed__12_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__12);
v___x_2033_ = l_Lean_indentExpr(v_a_1898_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_kw_2031_, v___x_2034_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_kw_2031_);
return v___x_2035_;
}
v___jp_1905_:
{
uint8_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unbox(v_a_1893_);
lean_dec(v_a_1893_);
lean_inc(v_a_1895_);
v___x_1915_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(v_a_1895_, v_a_1898_, v___x_1914_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v_fst_1917_; lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2021_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v_fst_1917_ = lean_ctor_get(v_a_1916_, 0);
v_snd_1918_ = lean_ctor_get(v_a_1916_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1916_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1920_ = v_a_1916_;
v_isShared_1921_ = v_isSharedCheck_2021_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_inc(v_fst_1917_);
lean_dec(v_a_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2021_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_Elab_admitGoal(v_a_1895_, v___x_1891_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1922_, 1);
v___x_1923_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__7, &l_Lean_Elab_Tactic_evalImpossible___closed__7_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__7);
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__8));
v___x_1927_ = 2;
v___x_1928_ = lean_box(0);
lean_inc(v_fst_1917_);
v___x_1929_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1925_, v___x_1926_, v_fst_1917_, v___x_1927_, v___x_1928_, v___x_1899_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l_Lean_Expr_mvarId_x21(v_a_1930_);
lean_dec(v_a_1930_);
v___x_1932_ = lean_array_get_size(v_snd_1918_);
v___x_1933_ = lean_array_to_list(v_snd_1918_);
lean_inc(v___x_1931_);
v___x_1934_ = l_Lean_Meta_introNCore(v___x_1931_, v___x_1932_, v___x_1933_, v___x_1824_, v___x_1824_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_snd_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1995_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_snd_1936_ = lean_ctor_get(v_a_1935_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_a_1935_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_a_1935_, 0);
lean_dec(v_unused_1996_);
v___x_1938_ = v_a_1935_;
v_isShared_1939_ = v_isSharedCheck_1995_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snd_1936_);
lean_dec(v_a_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1995_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_box(0);
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 1);
lean_ctor_set(v___x_1938_, 1, v___x_1940_);
lean_ctor_set(v___x_1938_, 0, v_snd_1936_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_snd_1936_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_1942_, v___y_1907_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref_known(v___x_1943_, 1);
v___x_1944_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_1901_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed), 11, 1);
lean_closure_set(v___f_1946_, 0, v_a_1945_);
v___x_1947_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v___f_1904_, v___f_1946_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v_a_1952_; lean_object* v___x_1953_; 
lean_dec_ref_known(v___x_1947_, 1);
v___x_1948_ = l_Lean_mkMVar(v___x_1931_);
v___x_1949_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v___x_1948_, v___y_1911_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_fst_1917_, v___y_1911_);
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_a_1952_, v_a_1950_, v___x_1824_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1990_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__10));
v___x_1956_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v___x_1955_, v___y_1913_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1990_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1990_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_levelParams_1961_; lean_object* v_type_1962_; lean_object* v_value_1963_; lean_object* v___x_1964_; lean_object* v_toCold_1965_; lean_object* v_options_1966_; lean_object* v_currRecDepth_1967_; lean_object* v_ref_1968_; lean_object* v_currNamespace_1969_; lean_object* v_openDecls_1970_; lean_object* v_initHeartbeats_1971_; lean_object* v_maxHeartbeats_1972_; lean_object* v_currMacroScope_1973_; uint8_t v_suppressElabErrors_1974_; lean_object* v_env_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v_levelParams_1961_ = lean_ctor_get(v_a_1954_, 0);
lean_inc_ref(v_levelParams_1961_);
v_type_1962_ = lean_ctor_get(v_a_1954_, 1);
lean_inc_ref(v_type_1962_);
v_value_1963_ = lean_ctor_get(v_a_1954_, 2);
lean_inc_ref(v_value_1963_);
lean_dec(v_a_1954_);
v___x_1964_ = lean_st_ref_get(v___y_1913_);
v_toCold_1965_ = lean_ctor_get(v___y_1912_, 0);
v_options_1966_ = lean_ctor_get(v___y_1912_, 1);
v_currRecDepth_1967_ = lean_ctor_get(v___y_1912_, 2);
v_ref_1968_ = lean_ctor_get(v___y_1912_, 4);
v_currNamespace_1969_ = lean_ctor_get(v___y_1912_, 5);
v_openDecls_1970_ = lean_ctor_get(v___y_1912_, 6);
v_initHeartbeats_1971_ = lean_ctor_get(v___y_1912_, 7);
v_maxHeartbeats_1972_ = lean_ctor_get(v___y_1912_, 8);
v_currMacroScope_1973_ = lean_ctor_get(v___y_1912_, 9);
v_suppressElabErrors_1974_ = lean_ctor_get_uint8(v___y_1912_, sizeof(void*)*10 + 1);
v_env_1975_ = lean_ctor_get(v___x_1964_, 0);
lean_inc_ref(v_env_1975_);
lean_dec(v___x_1964_);
v___x_1976_ = lean_array_to_list(v_levelParams_1961_);
lean_inc(v_a_1957_);
v___x_1977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1957_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
lean_ctor_set(v___x_1977_, 2, v_type_1962_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
lean_ctor_set(v___x_1920_, 1, v___x_1940_);
lean_ctor_set(v___x_1920_, 0, v_a_1957_);
v___x_1979_ = v___x_1920_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1957_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1940_);
v___x_1979_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v_value_1963_);
lean_ctor_set(v___x_1980_, 2, v___x_1979_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 2);
lean_ctor_set(v___x_1959_, 0, v___x_1980_);
v___x_1982_ = v___x_1959_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; uint8_t v___x_1987_; 
v___x_1983_ = l_Lean_Elab_async;
lean_inc_ref(v_options_1966_);
v___x_1984_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v_options_1966_, v___x_1983_, v___x_1824_);
v___x_1985_ = l_Lean_diagnostics;
v___x_1986_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_1984_, v___x_1985_);
v___x_1987_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1975_);
lean_dec_ref(v_env_1975_);
if (v___x_1986_ == 0)
{
if (v___x_1987_ == 0)
{
v___y_1826_ = v_a_1924_;
v___y_1827_ = v___x_1984_;
v___y_1828_ = v___x_1982_;
v___y_1829_ = v___y_1907_;
v___y_1830_ = v___x_1986_;
v_toCold_1831_ = v_toCold_1965_;
v_currRecDepth_1832_ = v_currRecDepth_1967_;
v_ref_1833_ = v_ref_1968_;
v_currNamespace_1834_ = v_currNamespace_1969_;
v_openDecls_1835_ = v_openDecls_1970_;
v_initHeartbeats_1836_ = v_initHeartbeats_1971_;
v_maxHeartbeats_1837_ = v_maxHeartbeats_1972_;
v_currMacroScope_1838_ = v_currMacroScope_1973_;
v_suppressElabErrors_1839_ = v_suppressElabErrors_1974_;
v___y_1840_ = v___y_1913_;
goto v___jp_1825_;
}
else
{
v___y_1863_ = v_a_1924_;
v___y_1864_ = v___x_1984_;
v___y_1865_ = v___y_1912_;
v___y_1866_ = v___x_1982_;
v___y_1867_ = v___y_1907_;
v___y_1868_ = v___x_1986_;
v___y_1869_ = v___y_1913_;
v___y_1870_ = v___x_1986_;
goto v___jp_1862_;
}
}
else
{
v___y_1863_ = v_a_1924_;
v___y_1864_ = v___x_1984_;
v___y_1865_ = v___y_1912_;
v___y_1866_ = v___x_1982_;
v___y_1867_ = v___y_1907_;
v___y_1868_ = v___x_1986_;
v___y_1869_ = v___y_1913_;
v___y_1870_ = v___x_1987_;
goto v___jp_1862_;
}
}
}
}
}
else
{
lean_object* v_a_1991_; 
lean_del_object(v___x_1920_);
v_a_1991_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1953_, 1);
v___y_1795_ = v_a_1924_;
v___y_1796_ = v___y_1907_;
v_a_1797_ = v_a_1991_;
goto v___jp_1794_;
}
}
else
{
lean_object* v_a_1992_; 
lean_dec(v___x_1931_);
lean_del_object(v___x_1920_);
lean_dec(v_fst_1917_);
v_a_1992_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1947_, 1);
v___y_1795_ = v_a_1924_;
v___y_1796_ = v___y_1907_;
v_a_1797_ = v_a_1992_;
goto v___jp_1794_;
}
}
else
{
lean_object* v_a_1993_; 
lean_dec(v___x_1931_);
lean_del_object(v___x_1920_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
v_a_1993_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1944_, 1);
v___y_1795_ = v_a_1924_;
v___y_1796_ = v___y_1907_;
v_a_1797_ = v_a_1993_;
goto v___jp_1794_;
}
}
else
{
lean_dec(v___x_1931_);
lean_del_object(v___x_1920_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
v___y_1808_ = v_a_1924_;
v___y_1809_ = v___y_1907_;
v___y_1810_ = v___x_1943_;
goto v___jp_1807_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v___x_1931_);
lean_dec(v_a_1924_);
lean_del_object(v___x_1920_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
v_a_1997_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1934_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1934_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1924_);
lean_del_object(v___x_1920_);
lean_dec(v_snd_1918_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
v_a_2005_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1929_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1929_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_1920_);
lean_dec(v_snd_1918_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
v_a_2013_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1923_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1923_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_del_object(v___x_1920_);
lean_dec(v_snd_1918_);
lean_dec(v_fst_1917_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
return v___x_1922_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1901_);
lean_dec(v_a_1895_);
v_a_2022_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1915_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1915_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_1895_);
lean_dec(v_a_1893_);
v_a_2036_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_1897_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_1897_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_1893_);
v_a_2044_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_1894_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_1894_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_a_2052_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1892_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1892_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
v___jp_1794_:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1798_, 0);
lean_dec(v_unused_1806_);
v___x_1800_ = v___x_1798_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v___x_1798_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 1);
lean_ctor_set(v___x_1800_, 0, v_a_1797_);
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1797_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_dec_ref(v_a_1797_);
return v___x_1798_;
}
}
v___jp_1807_:
{
if (lean_obj_tag(v___y_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___y_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___y_1810_, 1);
v___x_1812_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1812_, 0);
lean_dec(v_unused_1820_);
v___x_1814_ = v___x_1812_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v___x_1812_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_a_1811_);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_dec(v_a_1811_);
return v___x_1812_;
}
}
else
{
lean_object* v_a_1821_; 
v_a_1821_ = lean_ctor_get(v___y_1810_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___y_1810_, 1);
v___y_1795_ = v___y_1808_;
v___y_1796_ = v___y_1809_;
v_a_1797_ = v_a_1821_;
goto v___jp_1794_;
}
}
v___jp_1825_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1841_ = l_Lean_maxRecDepth;
v___x_1842_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v___y_1827_, v___x_1841_);
lean_inc(v_currMacroScope_1838_);
lean_inc(v_maxHeartbeats_1837_);
lean_inc(v_initHeartbeats_1836_);
lean_inc(v_openDecls_1835_);
lean_inc(v_currNamespace_1834_);
lean_inc(v_ref_1833_);
lean_inc(v_currRecDepth_1832_);
lean_inc_ref(v_toCold_1831_);
v___x_1843_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1843_, 0, v_toCold_1831_);
lean_ctor_set(v___x_1843_, 1, v___y_1827_);
lean_ctor_set(v___x_1843_, 2, v_currRecDepth_1832_);
lean_ctor_set(v___x_1843_, 3, v___x_1842_);
lean_ctor_set(v___x_1843_, 4, v_ref_1833_);
lean_ctor_set(v___x_1843_, 5, v_currNamespace_1834_);
lean_ctor_set(v___x_1843_, 6, v_openDecls_1835_);
lean_ctor_set(v___x_1843_, 7, v_initHeartbeats_1836_);
lean_ctor_set(v___x_1843_, 8, v_maxHeartbeats_1837_);
lean_ctor_set(v___x_1843_, 9, v_currMacroScope_1838_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*10, v___y_1830_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*10 + 1, v_suppressElabErrors_1839_);
v___x_1844_ = l_Lean_addDecl(v___y_1828_, v___x_1824_, v___x_1843_, v___y_1840_);
lean_dec_ref_known(v___x_1843_, 10);
v___y_1808_ = v___y_1826_;
v___y_1809_ = v___y_1829_;
v___y_1810_ = v___x_1844_;
goto v___jp_1807_;
}
v___jp_1845_:
{
lean_object* v_toCold_1853_; lean_object* v_currRecDepth_1854_; lean_object* v_ref_1855_; lean_object* v_currNamespace_1856_; lean_object* v_openDecls_1857_; lean_object* v_initHeartbeats_1858_; lean_object* v_maxHeartbeats_1859_; lean_object* v_currMacroScope_1860_; uint8_t v_suppressElabErrors_1861_; 
v_toCold_1853_ = lean_ctor_get(v___y_1851_, 0);
v_currRecDepth_1854_ = lean_ctor_get(v___y_1851_, 2);
v_ref_1855_ = lean_ctor_get(v___y_1851_, 4);
v_currNamespace_1856_ = lean_ctor_get(v___y_1851_, 5);
v_openDecls_1857_ = lean_ctor_get(v___y_1851_, 6);
v_initHeartbeats_1858_ = lean_ctor_get(v___y_1851_, 7);
v_maxHeartbeats_1859_ = lean_ctor_get(v___y_1851_, 8);
v_currMacroScope_1860_ = lean_ctor_get(v___y_1851_, 9);
v_suppressElabErrors_1861_ = lean_ctor_get_uint8(v___y_1851_, sizeof(void*)*10 + 1);
v___y_1826_ = v___y_1846_;
v___y_1827_ = v___y_1847_;
v___y_1828_ = v___y_1848_;
v___y_1829_ = v___y_1849_;
v___y_1830_ = v___y_1850_;
v_toCold_1831_ = v_toCold_1853_;
v_currRecDepth_1832_ = v_currRecDepth_1854_;
v_ref_1833_ = v_ref_1855_;
v_currNamespace_1834_ = v_currNamespace_1856_;
v_openDecls_1835_ = v_openDecls_1857_;
v_initHeartbeats_1836_ = v_initHeartbeats_1858_;
v_maxHeartbeats_1837_ = v_maxHeartbeats_1859_;
v_currMacroScope_1838_ = v_currMacroScope_1860_;
v_suppressElabErrors_1839_ = v_suppressElabErrors_1861_;
v___y_1840_ = v___y_1852_;
goto v___jp_1825_;
}
v___jp_1862_:
{
if (v___y_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v_env_1872_; lean_object* v_nextMacroScope_1873_; lean_object* v_ngen_1874_; lean_object* v_auxDeclNGen_1875_; lean_object* v_traceState_1876_; lean_object* v_messages_1877_; lean_object* v_infoState_1878_; lean_object* v_snapshotTasks_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1889_; 
v___x_1871_ = lean_st_ref_take(v___y_1869_);
v_env_1872_ = lean_ctor_get(v___x_1871_, 0);
v_nextMacroScope_1873_ = lean_ctor_get(v___x_1871_, 1);
v_ngen_1874_ = lean_ctor_get(v___x_1871_, 2);
v_auxDeclNGen_1875_ = lean_ctor_get(v___x_1871_, 3);
v_traceState_1876_ = lean_ctor_get(v___x_1871_, 4);
v_messages_1877_ = lean_ctor_get(v___x_1871_, 6);
v_infoState_1878_ = lean_ctor_get(v___x_1871_, 7);
v_snapshotTasks_1879_ = lean_ctor_get(v___x_1871_, 8);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1871_, 5);
lean_dec(v_unused_1890_);
v___x_1881_ = v___x_1871_;
v_isShared_1882_ = v_isSharedCheck_1889_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snapshotTasks_1879_);
lean_inc(v_infoState_1878_);
lean_inc(v_messages_1877_);
lean_inc(v_traceState_1876_);
lean_inc(v_auxDeclNGen_1875_);
lean_inc(v_ngen_1874_);
lean_inc(v_nextMacroScope_1873_);
lean_inc(v_env_1872_);
lean_dec(v___x_1871_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1889_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1883_ = l_Lean_Kernel_enableDiag(v_env_1872_, v___y_1868_);
v___x_1884_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__2, &l_Lean_Elab_Tactic_evalImpossible___closed__2_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__2);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 5, v___x_1884_);
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1886_ = v___x_1881_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_nextMacroScope_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_ngen_1874_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_auxDeclNGen_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_traceState_1876_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_messages_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_infoState_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_snapshotTasks_1879_);
v___x_1886_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_st_ref_put(v___y_1869_, v___x_1886_);
v___y_1846_ = v___y_1863_;
v___y_1847_ = v___y_1864_;
v___y_1848_ = v___y_1866_;
v___y_1849_ = v___y_1867_;
v___y_1850_ = v___y_1868_;
v___y_1851_ = v___y_1865_;
v___y_1852_ = v___y_1869_;
goto v___jp_1845_;
}
}
}
else
{
v___y_1846_ = v___y_1863_;
v___y_1847_ = v___y_1864_;
v___y_1848_ = v___y_1866_;
v___y_1849_ = v___y_1867_;
v___y_1850_ = v___y_1868_;
v___y_1851_ = v___y_1865_;
v___y_1852_ = v___y_1869_;
goto v___jp_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___boxed(lean_object* v_stx_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Elab_Tactic_evalImpossible(v_stx_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_stx_2060_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___boxed(lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(lean_object* v_00_u03b1_2091_, lean_object* v_x_2092_, lean_object* v_mkInfoTree_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_2092_, v_mkInfoTree_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_x_2105_, lean_object* v_mkInfoTree_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(v_00_u03b1_2104_, v_x_2105_, v_mkInfoTree_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(lean_object* v_00_u03b1_2117_, lean_object* v_ref_2118_, lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_2118_, v_msg_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(v_00_u03b1_2130_, v_ref_2131_, v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v_ref_2131_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(lean_object* v_00_u03b1_2143_, lean_object* v_msg_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_2144_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(v_00_u03b1_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1(){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2181_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1));
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4));
v___x_2184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___boxed), 10, 0);
v___x_2185_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2181_, v___x_2182_, v___x_2183_, v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___boxed(lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
return v_res_2187_;
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
