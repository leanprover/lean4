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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_value;
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
uint8_t v___x_3632__boxed_182_; lean_object* v_res_183_; 
v___x_3632__boxed_182_ = lean_unbox(v___x_173_);
v_res_183_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(v___x_3632__boxed_182_, v___x_174_, v_ms_175_, v_revBody_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
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
v_options_452_ = lean_ctor_get(v___y_444_, 2);
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
v_ref_469_ = lean_ctor_get(v___y_466_, 5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(lean_object* v_ctor_491_, lean_object* v_args_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0));
v___x_520_ = lean_string_dec_eq(v_ctor_491_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_get_size(v_args_492_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2);
v___x_526_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v___x_525_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
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
goto v___jp_498_;
}
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = l_Lean_instInhabitedExpr;
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get_borrowed(v___x_499_, v_args_492_, v___x_500_);
lean_inc(v___x_501_);
v___x_502_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_501_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_535_, lean_object* v_args_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(v_ctor_535_, v_args_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec_ref(v_args_536_);
lean_dec_ref(v_ctor_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___f_559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0));
v___x_560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_561_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_560_, v___f_559_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed(lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(lean_object* v_00_u03b1_569_, lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(v_00_u03b1_577_, v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_588_ = l_Lean_Expr_const___override(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0));
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3, &l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3);
return v___x_594_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(1);
v___x_596_ = l_Lean_MessageData_ofFormat(v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_601_ = l_Lean_MessageData_ofFormat(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
return v_x_602_;
}
else
{
lean_object* v_head_604_; lean_object* v_tail_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_627_; 
v_head_604_ = lean_ctor_get(v_x_603_, 0);
v_tail_605_ = lean_ctor_get(v_x_603_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_627_ == 0)
{
v___x_607_ = v_x_603_;
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_tail_605_);
lean_inc(v_head_604_);
lean_dec(v_x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_before_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_625_; 
v_before_609_ = lean_ctor_get(v_head_604_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_head_604_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_head_604_, 1);
lean_dec(v_unused_626_);
v___x_611_ = v_head_604_;
v_isShared_612_ = v_isSharedCheck_625_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_before_609_);
lean_dec(v_head_604_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_625_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 7);
lean_ctor_set(v___x_611_, 1, v___x_613_);
lean_ctor_set(v___x_611_, 0, v_x_602_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_x_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_624_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 7);
lean_ctor_set(v___x_607_, 1, v___x_616_);
lean_ctor_set(v___x_607_, 0, v___x_615_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_623_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = l_Lean_MessageData_ofSyntax(v_before_609_);
v___x_620_ = l_Lean_indentD(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v_x_602_ = v___x_621_;
v_x_603_ = v_tail_605_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_628_, lean_object* v_opt_629_){
_start:
{
lean_object* v_name_630_; lean_object* v_defValue_631_; lean_object* v_map_632_; lean_object* v___x_633_; 
v_name_630_ = lean_ctor_get(v_opt_629_, 0);
v_defValue_631_ = lean_ctor_get(v_opt_629_, 1);
v_map_632_ = lean_ctor_get(v_opts_628_, 0);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_632_, v_name_630_);
if (lean_obj_tag(v___x_633_) == 0)
{
uint8_t v___x_634_; 
v___x_634_ = lean_unbox(v_defValue_631_);
return v___x_634_;
}
else
{
lean_object* v_val_635_; 
v_val_635_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___x_633_, 1);
if (lean_obj_tag(v_val_635_) == 1)
{
uint8_t v_v_636_; 
v_v_636_ = lean_ctor_get_uint8(v_val_635_, 0);
lean_dec_ref_known(v_val_635_, 0);
return v_v_636_;
}
else
{
uint8_t v___x_637_; 
lean_dec(v_val_635_);
v___x_637_ = lean_unbox(v_defValue_631_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_638_, lean_object* v_opt_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_638_, v_opt_639_);
lean_dec_ref(v_opt_639_);
lean_dec_ref(v_opts_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_646_ = l_Lean_MessageData_ofFormat(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_647_, lean_object* v_macroStack_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_options_651_; lean_object* v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; 
v_options_651_ = lean_ctor_get(v___y_649_, 2);
v___x_652_ = l_Lean_Elab_pp_macroStack;
v___x_653_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_651_, v___x_652_);
v___x_654_ = lean_bool_not(v___x_653_);
if (v___x_654_ == 0)
{
if (lean_obj_tag(v_macroStack_648_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_msgData_647_);
return v___x_655_;
}
else
{
lean_object* v_head_656_; lean_object* v_after_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_672_; 
v_head_656_ = lean_ctor_get(v_macroStack_648_, 0);
lean_inc(v_head_656_);
v_after_657_ = lean_ctor_get(v_head_656_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_head_656_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_head_656_, 0);
lean_dec(v_unused_673_);
v___x_659_ = v_head_656_;
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_after_657_);
lean_dec(v_head_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 7);
lean_ctor_set(v___x_659_, 1, v___x_661_);
lean_ctor_set(v___x_659_, 0, v_msgData_647_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_msgData_647_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_671_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_msgData_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_664_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_MessageData_ofSyntax(v_after_657_);
v___x_667_ = l_Lean_indentD(v___x_666_);
v_msgData_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_668_, 0, v___x_665_);
lean_ctor_set(v_msgData_668_, 1, v___x_667_);
v___x_669_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_668_, v_macroStack_648_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v_macroStack_648_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_msgData_647_);
return v___x_674_;
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
lean_object* v_ref_688_; lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v_macroStack_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_ref_688_ = lean_ctor_get(v___y_685_, 5);
v___x_689_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_680_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref(v___x_689_);
v_macroStack_691_ = lean_ctor_get(v___y_681_, 1);
v___x_692_ = l_Lean_Elab_getBetterRef(v_ref_688_, v_macroStack_691_);
lean_inc(v_macroStack_691_);
v___x_693_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_690_, v_macroStack_691_, v___y_685_);
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
lean_ctor_set(v___x_698_, 0, v___x_692_);
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
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = l_Lean_Expr_hasMVar(v_e_720_);
v___x_724_ = lean_bool_not(v___x_723_);
if (v___x_724_ == 0)
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
v___x_740_ = lean_st_ref_set(v___y_721_, v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_fst_728_);
return v___x_741_;
}
}
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_e_720_);
return v___x_745_;
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
lean_object* v_ty_x3f_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_fileName_784_; lean_object* v_fileMap_785_; lean_object* v_options_786_; lean_object* v_currRecDepth_787_; lean_object* v_maxRecDepth_788_; lean_object* v_ref_789_; lean_object* v_currNamespace_790_; lean_object* v_openDecls_791_; lean_object* v_initHeartbeats_792_; lean_object* v_maxHeartbeats_793_; lean_object* v_quotContext_794_; lean_object* v_currMacroScope_795_; uint8_t v_diag_796_; lean_object* v_cancelTk_x3f_797_; uint8_t v_suppressElabErrors_798_; lean_object* v_inheritedTraceOptions_799_; uint8_t v___x_800_; lean_object* v_ref_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
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
v_fileName_784_ = lean_ctor_get(v_a_775_, 0);
v_fileMap_785_ = lean_ctor_get(v_a_775_, 1);
v_options_786_ = lean_ctor_get(v_a_775_, 2);
v_currRecDepth_787_ = lean_ctor_get(v_a_775_, 3);
v_maxRecDepth_788_ = lean_ctor_get(v_a_775_, 4);
v_ref_789_ = lean_ctor_get(v_a_775_, 5);
v_currNamespace_790_ = lean_ctor_get(v_a_775_, 6);
v_openDecls_791_ = lean_ctor_get(v_a_775_, 7);
v_initHeartbeats_792_ = lean_ctor_get(v_a_775_, 8);
v_maxHeartbeats_793_ = lean_ctor_get(v_a_775_, 9);
v_quotContext_794_ = lean_ctor_get(v_a_775_, 10);
v_currMacroScope_795_ = lean_ctor_get(v_a_775_, 11);
v_diag_796_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*14);
v_cancelTk_x3f_797_ = lean_ctor_get(v_a_775_, 12);
v_suppressElabErrors_798_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_799_ = lean_ctor_get(v_a_775_, 13);
v___x_800_ = 1;
v_ref_801_ = l_Lean_replaceRef(v_stx_770_, v_ref_789_);
lean_dec(v_stx_770_);
lean_inc_ref(v_inheritedTraceOptions_799_);
lean_inc(v_cancelTk_x3f_797_);
lean_inc(v_currMacroScope_795_);
lean_inc(v_quotContext_794_);
lean_inc(v_maxHeartbeats_793_);
lean_inc(v_initHeartbeats_792_);
lean_inc(v_openDecls_791_);
lean_inc(v_currNamespace_790_);
lean_inc(v_maxRecDepth_788_);
lean_inc(v_currRecDepth_787_);
lean_inc_ref(v_options_786_);
lean_inc_ref(v_fileMap_785_);
lean_inc_ref(v_fileName_784_);
v___x_802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_802_, 0, v_fileName_784_);
lean_ctor_set(v___x_802_, 1, v_fileMap_785_);
lean_ctor_set(v___x_802_, 2, v_options_786_);
lean_ctor_set(v___x_802_, 3, v_currRecDepth_787_);
lean_ctor_set(v___x_802_, 4, v_maxRecDepth_788_);
lean_ctor_set(v___x_802_, 5, v_ref_801_);
lean_ctor_set(v___x_802_, 6, v_currNamespace_790_);
lean_ctor_set(v___x_802_, 7, v_openDecls_791_);
lean_ctor_set(v___x_802_, 8, v_initHeartbeats_792_);
lean_ctor_set(v___x_802_, 9, v_maxHeartbeats_793_);
lean_ctor_set(v___x_802_, 10, v_quotContext_794_);
lean_ctor_set(v___x_802_, 11, v_currMacroScope_795_);
lean_ctor_set(v___x_802_, 12, v_cancelTk_x3f_797_);
lean_ctor_set(v___x_802_, 13, v_inheritedTraceOptions_799_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*14, v_diag_796_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*14 + 1, v_suppressElabErrors_798_);
v___x_803_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_783_, v___x_800_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v___x_802_, v_a_776_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___y_817_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___x_901_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_804_, v_a_774_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___x_805_);
v___x_901_ = l_Lean_Expr_hasSorry(v_a_806_);
if (v___x_901_ == 0)
{
v___y_846_ = v_a_771_;
v___y_847_ = v_a_772_;
v___y_848_ = v_a_773_;
v___y_849_ = v_a_774_;
v___y_850_ = v___x_802_;
v___y_851_ = v_a_776_;
goto v___jp_845_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_Expr_hasSyntheticSorry(v_a_806_);
if (v___x_902_ == 0)
{
v___y_883_ = v_a_771_;
v___y_884_ = v_a_772_;
v___y_885_ = v_a_773_;
v___y_886_ = v_a_774_;
v___y_887_ = v___x_802_;
v___y_888_ = v_a_776_;
goto v___jp_882_;
}
else
{
lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_806_);
lean_dec_ref_known(v___x_802_, 14);
v___x_903_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
v___jp_807_:
{
if (v___y_817_ == 0)
{
if (lean_obj_tag(v___y_811_) == 0)
{
lean_dec_ref_known(v___y_811_, 2);
lean_dec_ref(v___y_813_);
lean_dec(v_a_806_);
return v___y_816_;
}
else
{
lean_object* v_id_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_id_818_ = lean_ctor_get(v___y_811_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___y_811_, 1);
lean_dec(v_unused_832_);
v___x_820_ = v___y_811_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_id_818_);
lean_dec(v___y_811_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_instBEqInternalExceptionId_beq(v___y_810_, v_id_818_);
lean_dec(v_id_818_);
if (v___x_822_ == 0)
{
lean_del_object(v___x_820_);
lean_dec_ref(v___y_813_);
lean_dec(v_a_806_);
return v___y_816_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec_ref(v___y_816_);
v___x_823_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6);
v___x_824_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8);
v___x_825_ = l_Lean_indentExpr(v_a_806_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 7);
lean_ctor_set(v___x_820_, 1, v___x_825_);
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_827_ = v___x_820_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_823_);
v___x_829_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_828_, v___y_809_, v___y_812_, v___y_815_, v___y_808_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_813_);
return v___x_829_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_813_);
lean_dec_ref(v___y_811_);
lean_dec(v_a_806_);
return v___y_816_;
}
}
v___jp_833_:
{
lean_object* v___x_840_; 
lean_inc(v_a_806_);
v___x_840_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_806_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec_ref(v___y_838_);
lean_dec(v_a_806_);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
v___x_842_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_843_ = l_Lean_Exception_isInterrupt(v_a_841_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
lean_inc(v_a_841_);
v___x_844_ = l_Lean_Exception_isRuntime(v_a_841_);
v___y_808_ = v___y_837_;
v___y_809_ = v___y_834_;
v___y_810_ = v___x_842_;
v___y_811_ = v_a_841_;
v___y_812_ = v___y_835_;
v___y_813_ = v___y_838_;
v___y_814_ = v___y_839_;
v___y_815_ = v___y_836_;
v___y_816_ = v___x_840_;
v___y_817_ = v___x_844_;
goto v___jp_807_;
}
else
{
v___y_808_ = v___y_837_;
v___y_809_ = v___y_834_;
v___y_810_ = v___x_842_;
v___y_811_ = v_a_841_;
v___y_812_ = v___y_835_;
v___y_813_ = v___y_838_;
v___y_814_ = v___y_839_;
v___y_815_ = v___y_836_;
v___y_816_ = v___x_840_;
v___y_817_ = v___x_843_;
goto v___jp_807_;
}
}
}
v___jp_845_:
{
lean_object* v___x_852_; 
lean_inc(v_a_806_);
v___x_852_ = l_Lean_Meta_getMVars(v_a_806_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_853_, v___x_780_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v_a_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; uint8_t v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_unbox(v_a_855_);
lean_dec(v_a_855_);
if (v___x_856_ == 0)
{
v___y_834_ = v___y_846_;
v___y_835_ = v___y_847_;
v___y_836_ = v___y_848_;
v___y_837_ = v___y_849_;
v___y_838_ = v___y_850_;
v___y_839_ = v___y_851_;
goto v___jp_833_;
}
else
{
lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___y_850_);
lean_dec(v_a_806_);
v___x_857_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___y_850_);
lean_dec(v_a_806_);
v_a_866_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_854_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v___y_850_);
lean_dec(v_a_806_);
v_a_874_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_852_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_852_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
v___jp_882_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v___x_889_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10);
v___x_890_ = l_Lean_indentExpr(v_a_806_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_891_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec_ref(v___y_887_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref_known(v___x_802_, 14);
v_a_912_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_803_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_803_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_stx_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(uint8_t v_config_939_, lean_object* v_item_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_item_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_959_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_940_, v___x_958_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_959_) == 0)
{
uint8_t v___x_960_; 
lean_dec_ref_known(v___x_959_, 1);
v___x_960_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_940_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_961_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_940_);
lean_inc_ref(v_item_940_);
v___x_962_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_940_);
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1));
v___x_964_ = lean_string_dec_eq(v___x_961_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2));
v___x_966_ = lean_string_dec_eq(v___x_961_, v___x_965_);
lean_dec_ref(v___x_961_);
if (v___x_966_ == 0)
{
lean_dec_ref(v_item_940_);
v_item_949_ = v___x_962_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
v___y_952_ = v___y_943_;
v___y_953_ = v___y_944_;
v___y_954_ = v___y_945_;
v___y_955_ = v___y_946_;
goto v___jp_948_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3));
v___x_968_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_940_, v___x_967_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_968_) == 0)
{
uint8_t v___x_969_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_969_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_962_);
if (v___x_969_ == 0)
{
lean_dec_ref(v_item_940_);
v_item_949_ = v___x_962_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
v___y_952_ = v___y_943_;
v___y_953_ = v___y_944_;
v___y_954_ = v___y_945_;
v___y_955_ = v___y_946_;
goto v___jp_948_;
}
else
{
lean_object* v___x_970_; 
lean_dec_ref(v___x_962_);
v___x_970_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_970_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_970_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___x_962_);
lean_dec_ref(v_item_940_);
v_a_987_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_968_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_968_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
else
{
uint8_t v___x_995_; 
lean_dec_ref(v___x_961_);
v___x_995_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_962_);
if (v___x_995_ == 0)
{
lean_dec_ref(v_item_940_);
v_item_949_ = v___x_962_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
v___y_952_ = v___y_943_;
v___y_953_ = v___y_944_;
v___y_954_ = v___y_945_;
v___y_955_ = v___y_946_;
goto v___jp_948_;
}
else
{
lean_object* v_value_996_; lean_object* v___x_997_; 
lean_dec_ref(v___x_962_);
v_value_996_ = lean_ctor_get(v_item_940_, 2);
lean_inc(v_value_996_);
lean_dec_ref(v_item_940_);
v___x_997_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_value_996_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_997_;
}
}
}
else
{
v_item_949_ = v_item_940_;
v___y_950_ = v___y_941_;
v___y_951_ = v___y_942_;
v___y_952_ = v___y_943_;
v___y_953_ = v___y_944_;
v___y_954_ = v___y_945_;
v___y_955_ = v___y_946_;
goto v___jp_948_;
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_item_940_);
v_a_998_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_959_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_959_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
v___jp_948_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0));
v___x_957_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_949_, v___x_956_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1006_, lean_object* v_item_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v_config_4003__boxed_1015_; lean_object* v_res_1016_; 
v_config_4003__boxed_1015_ = lean_unbox(v_config_1006_);
v_res_1016_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(v_config_4003__boxed_1015_, v_item_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1019_, v___y_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(v_e_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1065_, v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1075_, lean_object* v_macroStack_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1075_, v_macroStack_1076_, v___y_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1085_, lean_object* v_macroStack_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1085_, v_macroStack_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5));
v___x_1097_ = l_Lean_mkConst(v___x_1096_, v___x_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(uint8_t v_cfg_1100_, lean_object* v_cfgItem_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1);
v___x_1110_ = lean_box(v_cfg_1100_);
v___x_1111_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_1110_, v_cfgItem_1101_, v___x_1109_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed(lean_object* v_cfg_1112_, lean_object* v_cfgItem_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_cfg_boxed_1121_; lean_object* v_res_1122_; 
v_cfg_boxed_1121_ = lean_unbox(v_cfg_1112_);
v_res_1122_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(v_cfg_boxed_1121_, v_cfgItem_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_cfgItem_1113_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(lean_object* v_cfg_1124_, uint8_t v_init_1125_, uint8_t v_logExceptions_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_onErr_1131_; lean_object* v_eval_1132_; 
v_onErr_1131_ = ((lean_object*)(l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0));
v_eval_1132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0));
if (v_logExceptions_1126_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(v_init_1125_);
v___x_1134_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1132_, v___x_1133_, v_cfg_1124_, v_onErr_1131_, v_logExceptions_1126_, v_a_1128_, v_a_1129_);
return v___x_1134_;
}
else
{
uint8_t v_recover_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_recover_1135_ = lean_ctor_get_uint8(v_a_1127_, sizeof(void*)*1);
v___x_1136_ = lean_box(v_init_1125_);
v___x_1137_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1132_, v___x_1136_, v_cfg_1124_, v_onErr_1131_, v_recover_1135_, v_a_1128_, v_a_1129_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___boxed(lean_object* v_cfg_1138_, lean_object* v_init_1139_, lean_object* v_logExceptions_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_init_boxed_1145_; uint8_t v_logExceptions_boxed_1146_; lean_object* v_res_1147_; 
v_init_boxed_1145_ = lean_unbox(v_init_1139_);
v_logExceptions_boxed_1146_ = lean_unbox(v_logExceptions_1140_);
v_res_1147_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1138_, v_init_boxed_1145_, v_logExceptions_boxed_1146_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig(lean_object* v_cfg_1148_, uint8_t v_init_1149_, uint8_t v_logExceptions_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v_cfg_1148_, v_init_1149_, v_logExceptions_1150_, v_a_1151_, v_a_1157_, v_a_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabImpossibleConfig___boxed(lean_object* v_cfg_1161_, lean_object* v_init_1162_, lean_object* v_logExceptions_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_init_boxed_1173_; uint8_t v_logExceptions_boxed_1174_; lean_object* v_res_1175_; 
v_init_boxed_1173_ = lean_unbox(v_init_1162_);
v_logExceptions_boxed_1174_ = lean_unbox(v_logExceptions_1163_);
v_res_1175_ = l_Lean_Elab_Tactic_elabImpossibleConfig(v_cfg_1161_, v_init_boxed_1173_, v_logExceptions_boxed_1174_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(lean_object* v_e_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = l_Lean_Expr_hasMVar(v_e_1176_);
v___x_1180_ = lean_bool_not(v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v_mctx_1182_; lean_object* v___x_1183_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; lean_object* v___x_1186_; lean_object* v_cache_1187_; lean_object* v_zetaDeltaFVarIds_1188_; lean_object* v_postponed_1189_; lean_object* v_diag_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
v___x_1181_ = lean_st_ref_get(v___y_1177_);
v_mctx_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_mctx_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = l_Lean_instantiateMVarsCore(v_mctx_1182_, v_e_1176_);
v_fst_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_fst_1184_);
v_snd_1185_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_snd_1185_);
lean_dec_ref(v___x_1183_);
v___x_1186_ = lean_st_ref_take(v___y_1177_);
v_cache_1187_ = lean_ctor_get(v___x_1186_, 1);
v_zetaDeltaFVarIds_1188_ = lean_ctor_get(v___x_1186_, 2);
v_postponed_1189_ = lean_ctor_get(v___x_1186_, 3);
v_diag_1190_ = lean_ctor_get(v___x_1186_, 4);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___x_1186_, 0);
lean_dec(v_unused_1200_);
v___x_1192_ = v___x_1186_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_diag_1190_);
lean_inc(v_postponed_1189_);
lean_inc(v_zetaDeltaFVarIds_1188_);
lean_inc(v_cache_1187_);
lean_dec(v___x_1186_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_snd_1185_);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_snd_1185_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_cache_1187_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_zetaDeltaFVarIds_1188_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_postponed_1189_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_diag_1190_);
v___x_1195_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_st_ref_set(v___y_1177_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_fst_1184_);
return v___x_1197_;
}
}
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_e_1176_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg___boxed(lean_object* v_e_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1202_, v___y_1203_);
lean_dec(v___y_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(lean_object* v_e_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_e_1206_, v___y_1212_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___boxed(lean_object* v_e_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(v_e_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v___x_1238_ = lean_apply_9(v_x_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, lean_box(0));
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed(lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(v_x_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(lean_object* v_mvarId_1250_, lean_object* v_x_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; 
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1261_, 0, v_x_1251_);
lean_closure_set(v___f_1261_, 1, v___y_1252_);
lean_closure_set(v___f_1261_, 2, v___y_1253_);
lean_closure_set(v___f_1261_, 3, v___y_1254_);
lean_closure_set(v___f_1261_, 4, v___y_1255_);
v___x_1262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1250_, v___f_1261_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
return v___x_1262_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___boxed(lean_object* v_mvarId_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1271_, v_x_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(lean_object* v_00_u03b1_1283_, lean_object* v_mvarId_1284_, lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_mvarId_1284_, v_x_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_mvarId_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(v_00_u03b1_1296_, v_mvarId_1297_, v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(lean_object* v_kind_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_auxDeclNGen_1313_; lean_object* v___x_1314_; lean_object* v_env_1315_; lean_object* v___x_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; lean_object* v_env_1320_; lean_object* v_nextMacroScope_1321_; lean_object* v_ngen_1322_; lean_object* v_traceState_1323_; lean_object* v_cache_1324_; lean_object* v_messages_1325_; lean_object* v_infoState_1326_; lean_object* v_snapshotTasks_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1336_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_auxDeclNGen_1313_ = lean_ctor_get(v___x_1312_, 3);
lean_inc_ref(v_auxDeclNGen_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = lean_st_ref_get(v___y_1310_);
v_env_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref(v_env_1315_);
lean_dec(v___x_1314_);
v___x_1316_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_1315_, v_auxDeclNGen_1313_, v_kind_1309_);
v_fst_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v___x_1316_);
v___x_1319_ = lean_st_ref_take(v___y_1310_);
v_env_1320_ = lean_ctor_get(v___x_1319_, 0);
v_nextMacroScope_1321_ = lean_ctor_get(v___x_1319_, 1);
v_ngen_1322_ = lean_ctor_get(v___x_1319_, 2);
v_traceState_1323_ = lean_ctor_get(v___x_1319_, 4);
v_cache_1324_ = lean_ctor_get(v___x_1319_, 5);
v_messages_1325_ = lean_ctor_get(v___x_1319_, 6);
v_infoState_1326_ = lean_ctor_get(v___x_1319_, 7);
v_snapshotTasks_1327_ = lean_ctor_get(v___x_1319_, 8);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1319_, 3);
lean_dec(v_unused_1337_);
v___x_1329_ = v___x_1319_;
v_isShared_1330_ = v_isSharedCheck_1336_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_snapshotTasks_1327_);
lean_inc(v_infoState_1326_);
lean_inc(v_messages_1325_);
lean_inc(v_cache_1324_);
lean_inc(v_traceState_1323_);
lean_inc(v_ngen_1322_);
lean_inc(v_nextMacroScope_1321_);
lean_inc(v_env_1320_);
lean_dec(v___x_1319_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1336_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 3, v_snd_1318_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_env_1320_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_nextMacroScope_1321_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_ngen_1322_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_snd_1318_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_traceState_1323_);
lean_ctor_set(v_reuseFailAlloc_1335_, 5, v_cache_1324_);
lean_ctor_set(v_reuseFailAlloc_1335_, 6, v_messages_1325_);
lean_ctor_set(v_reuseFailAlloc_1335_, 7, v_infoState_1326_);
lean_ctor_set(v_reuseFailAlloc_1335_, 8, v_snapshotTasks_1327_);
v___x_1332_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_st_ref_set(v___y_1310_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_fst_1317_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg___boxed(lean_object* v_kind_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1338_, v___y_1339_);
lean_dec(v___y_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(lean_object* v_kind_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v_kind_1342_, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___boxed(lean_object* v_kind_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(v_kind_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(lean_object* v_opts_1364_, lean_object* v_opt_1365_){
_start:
{
lean_object* v_name_1366_; lean_object* v_defValue_1367_; lean_object* v_map_1368_; lean_object* v___x_1369_; 
v_name_1366_ = lean_ctor_get(v_opt_1365_, 0);
v_defValue_1367_ = lean_ctor_get(v_opt_1365_, 1);
v_map_1368_ = lean_ctor_get(v_opts_1364_, 0);
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1368_, v_name_1366_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_inc(v_defValue_1367_);
return v_defValue_1367_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
if (lean_obj_tag(v_val_1370_) == 3)
{
lean_object* v_v_1371_; 
v_v_1371_ = lean_ctor_get(v_val_1370_, 0);
lean_inc(v_v_1371_);
lean_dec_ref_known(v_val_1370_, 1);
return v_v_1371_;
}
else
{
lean_dec(v_val_1370_);
lean_inc(v_defValue_1367_);
return v_defValue_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(lean_object* v_opts_1372_, lean_object* v_opt_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v_opts_1372_, v_opt_1373_);
lean_dec_ref(v_opt_1373_);
lean_dec_ref(v_opts_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0(lean_object* v_a_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_MVarId_getType(v_a_1375_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_a_1386_, v___y_1381_);
return v___x_1387_;
}
else
{
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(lean_object* v_a_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Elab_Tactic_evalImpossible___lam__0(v_a_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1(lean_object* v___x_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Elab_Tactic_evalTactic(v___x_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref_known(v___x_1409_, 1);
v___x_1410_ = l_Lean_Elab_Tactic_done(v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1410_;
}
else
{
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(lean_object* v___x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Elab_Tactic_evalImpossible___lam__1(v___x_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2(lean_object* v_a_1422_, lean_object* v_trees_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
v___x_1433_ = lean_apply_9(v_a_1422_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_a_1434_);
lean_ctor_set(v___x_1438_, 1, v_trees_1423_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_trees_1423_);
v_a_1443_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1433_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1433_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed(lean_object* v_a_1451_, lean_object* v_trees_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Elab_Tactic_evalImpossible___lam__2(v_a_1451_, v_trees_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1462_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(32u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = ((size_t)5ULL);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_unsigned_to_nat(32u);
v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
v___x_1470_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0);
v___x_1471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1467_);
lean_ctor_set(v___x_1471_, 3, v___x_1467_);
lean_ctor_set_usize(v___x_1471_, 4, v___x_1466_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_infoState_1475_; lean_object* v_trees_1476_; lean_object* v___x_1477_; lean_object* v_infoState_1478_; lean_object* v_env_1479_; lean_object* v_nextMacroScope_1480_; lean_object* v_ngen_1481_; lean_object* v_auxDeclNGen_1482_; lean_object* v_traceState_1483_; lean_object* v_cache_1484_; lean_object* v_messages_1485_; lean_object* v_snapshotTasks_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1507_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_infoState_1475_ = lean_ctor_get(v___x_1474_, 7);
lean_inc_ref(v_infoState_1475_);
lean_dec(v___x_1474_);
v_trees_1476_ = lean_ctor_get(v_infoState_1475_, 2);
lean_inc_ref(v_trees_1476_);
lean_dec_ref(v_infoState_1475_);
v___x_1477_ = lean_st_ref_take(v___y_1472_);
v_infoState_1478_ = lean_ctor_get(v___x_1477_, 7);
v_env_1479_ = lean_ctor_get(v___x_1477_, 0);
v_nextMacroScope_1480_ = lean_ctor_get(v___x_1477_, 1);
v_ngen_1481_ = lean_ctor_get(v___x_1477_, 2);
v_auxDeclNGen_1482_ = lean_ctor_get(v___x_1477_, 3);
v_traceState_1483_ = lean_ctor_get(v___x_1477_, 4);
v_cache_1484_ = lean_ctor_get(v___x_1477_, 5);
v_messages_1485_ = lean_ctor_get(v___x_1477_, 6);
v_snapshotTasks_1486_ = lean_ctor_get(v___x_1477_, 8);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1488_ = v___x_1477_;
v_isShared_1489_ = v_isSharedCheck_1507_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snapshotTasks_1486_);
lean_inc(v_infoState_1478_);
lean_inc(v_messages_1485_);
lean_inc(v_cache_1484_);
lean_inc(v_traceState_1483_);
lean_inc(v_auxDeclNGen_1482_);
lean_inc(v_ngen_1481_);
lean_inc(v_nextMacroScope_1480_);
lean_inc(v_env_1479_);
lean_dec(v___x_1477_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1507_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v_enabled_1490_; lean_object* v_assignment_1491_; lean_object* v_lazyAssignment_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1505_; 
v_enabled_1490_ = lean_ctor_get_uint8(v_infoState_1478_, sizeof(void*)*3);
v_assignment_1491_ = lean_ctor_get(v_infoState_1478_, 0);
v_lazyAssignment_1492_ = lean_ctor_get(v_infoState_1478_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_infoState_1478_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_infoState_1478_, 2);
lean_dec(v_unused_1506_);
v___x_1494_ = v_infoState_1478_;
v_isShared_1495_ = v_isSharedCheck_1505_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_lazyAssignment_1492_);
lean_inc(v_assignment_1491_);
lean_dec(v_infoState_1478_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1505_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 2, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_assignment_1491_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_lazyAssignment_1492_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v___x_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3, v_enabled_1490_);
v___x_1498_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 7, v___x_1498_);
v___x_1500_ = v___x_1488_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_env_1479_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_nextMacroScope_1480_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_ngen_1481_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_auxDeclNGen_1482_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_traceState_1483_);
lean_ctor_set(v_reuseFailAlloc_1503_, 5, v_cache_1484_);
lean_ctor_set(v_reuseFailAlloc_1503_, 6, v_messages_1485_);
lean_ctor_set(v_reuseFailAlloc_1503_, 7, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 8, v_snapshotTasks_1486_);
v___x_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_st_ref_set(v___y_1472_, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_trees_1476_);
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___boxed(lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1508_);
lean_dec(v___y_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(lean_object* v___y_1511_, lean_object* v_mkInfoTree_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v_a_1520_, lean_object* v_a_x3f_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v_infoState_1524_; lean_object* v_trees_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_st_ref_get(v___y_1511_);
v_infoState_1524_ = lean_ctor_get(v___x_1523_, 7);
lean_inc_ref(v_infoState_1524_);
lean_dec(v___x_1523_);
v_trees_1525_ = lean_ctor_get(v_infoState_1524_, 2);
lean_inc_ref(v_trees_1525_);
lean_dec_ref(v_infoState_1524_);
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
v___x_1526_ = lean_apply_10(v_mkInfoTree_1512_, v_trees_1525_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1511_, lean_box(0));
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1565_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1565_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1565_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v_infoState_1532_; lean_object* v_env_1533_; lean_object* v_nextMacroScope_1534_; lean_object* v_ngen_1535_; lean_object* v_auxDeclNGen_1536_; lean_object* v_traceState_1537_; lean_object* v_cache_1538_; lean_object* v_messages_1539_; lean_object* v_snapshotTasks_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1564_; 
v___x_1531_ = lean_st_ref_take(v___y_1511_);
v_infoState_1532_ = lean_ctor_get(v___x_1531_, 7);
v_env_1533_ = lean_ctor_get(v___x_1531_, 0);
v_nextMacroScope_1534_ = lean_ctor_get(v___x_1531_, 1);
v_ngen_1535_ = lean_ctor_get(v___x_1531_, 2);
v_auxDeclNGen_1536_ = lean_ctor_get(v___x_1531_, 3);
v_traceState_1537_ = lean_ctor_get(v___x_1531_, 4);
v_cache_1538_ = lean_ctor_get(v___x_1531_, 5);
v_messages_1539_ = lean_ctor_get(v___x_1531_, 6);
v_snapshotTasks_1540_ = lean_ctor_get(v___x_1531_, 8);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1542_ = v___x_1531_;
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_snapshotTasks_1540_);
lean_inc(v_infoState_1532_);
lean_inc(v_messages_1539_);
lean_inc(v_cache_1538_);
lean_inc(v_traceState_1537_);
lean_inc(v_auxDeclNGen_1536_);
lean_inc(v_ngen_1535_);
lean_inc(v_nextMacroScope_1534_);
lean_inc(v_env_1533_);
lean_dec(v___x_1531_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v_enabled_1544_; lean_object* v_assignment_1545_; lean_object* v_lazyAssignment_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1562_; 
v_enabled_1544_ = lean_ctor_get_uint8(v_infoState_1532_, sizeof(void*)*3);
v_assignment_1545_ = lean_ctor_get(v_infoState_1532_, 0);
v_lazyAssignment_1546_ = lean_ctor_get(v_infoState_1532_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_infoState_1532_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_infoState_1532_, 2);
lean_dec(v_unused_1563_);
v___x_1548_ = v_infoState_1532_;
v_isShared_1549_ = v_isSharedCheck_1562_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_lazyAssignment_1546_);
lean_inc(v_assignment_1545_);
lean_dec(v_infoState_1532_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1562_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_PersistentArray_push___redArg(v_a_1520_, v_a_1527_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 2, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_assignment_1545_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_lazyAssignment_1546_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v___x_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*3, v_enabled_1544_);
v___x_1552_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 7, v___x_1552_);
v___x_1554_ = v___x_1542_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_env_1533_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_nextMacroScope_1534_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_ngen_1535_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_auxDeclNGen_1536_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_traceState_1537_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v_cache_1538_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_messages_1539_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v_snapshotTasks_1540_);
v___x_1554_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1555_ = lean_st_ref_set(v___y_1511_, v___x_1554_);
v___x_1556_ = lean_box(0);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1556_);
v___x_1558_ = v___x_1529_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_a_1520_);
v_a_1566_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1526_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1526_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0___boxed(lean_object* v___y_1574_, lean_object* v_mkInfoTree_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v_a_1583_, lean_object* v_a_x3f_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1574_, v_mkInfoTree_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v_a_1583_, v_a_x3f_1584_);
lean_dec(v_a_x3f_1584_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1574_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(lean_object* v_x_1587_, lean_object* v_mkInfoTree_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_infoState_1599_; uint8_t v_enabled_1600_; 
v___x_1598_ = lean_st_ref_get(v___y_1596_);
v_infoState_1599_ = lean_ctor_get(v___x_1598_, 7);
lean_inc_ref(v_infoState_1599_);
lean_dec(v___x_1598_);
v_enabled_1600_ = lean_ctor_get_uint8(v_infoState_1599_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1599_);
if (v_enabled_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v_mkInfoTree_1588_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
v___x_1601_ = lean_apply_9(v_x_1587_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, lean_box(0));
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v_r_1604_; 
v___x_1602_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_1596_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1602_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
v_r_1604_ = lean_apply_9(v_x_1587_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, lean_box(0));
if (lean_obj_tag(v_r_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1629_; 
v_a_1605_ = lean_ctor_get(v_r_1604_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_r_1604_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1607_ = v_r_1604_;
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_r_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
lean_inc(v_a_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1596_, v_mkInfoTree_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v_a_1603_, v___x_1610_);
lean_dec_ref(v___x_1610_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v___x_1611_, 0);
lean_dec(v_unused_1619_);
v___x_1613_ = v___x_1611_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v___x_1611_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_a_1605_);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1605_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_a_1605_);
v_a_1620_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v_r_1604_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v_r_1604_, 1);
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_1596_, v_mkInfoTree_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v_a_1603_, v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1640_);
v___x_1634_ = v___x_1632_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v___x_1632_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 1);
lean_ctor_set(v___x_1634_, 0, v_a_1630_);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1630_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1630_);
v_a_1641_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1632_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___boxed(lean_object* v_x_1649_, lean_object* v_mkInfoTree_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_1649_, v_mkInfoTree_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(lean_object* v_o_1664_, lean_object* v_k_1665_, uint8_t v_v_1666_){
_start:
{
lean_object* v_map_1667_; uint8_t v_hasTrace_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1682_; 
v_map_1667_ = lean_ctor_get(v_o_1664_, 0);
v_hasTrace_1668_ = lean_ctor_get_uint8(v_o_1664_, sizeof(void*)*1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_o_1664_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1670_ = v_o_1664_;
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_map_1667_);
lean_dec(v_o_1664_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1672_, 0, v_v_1666_);
lean_inc(v_k_1665_);
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1665_, v___x_1672_, v_map_1667_);
if (v_hasTrace_1668_ == 0)
{
lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1));
v___x_1675_ = l_Lean_Name_isPrefixOf(v___x_1674_, v_k_1665_);
lean_dec(v_k_1665_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1677_ = v___x_1670_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1673_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*1, v___x_1675_);
return v___x_1677_;
}
}
else
{
lean_object* v___x_1680_; 
lean_dec(v_k_1665_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1680_ = v___x_1670_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1681_, sizeof(void*)*1, v_hasTrace_1668_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___boxed(lean_object* v_o_1683_, lean_object* v_k_1684_, lean_object* v_v_1685_){
_start:
{
uint8_t v_v_boxed_1686_; lean_object* v_res_1687_; 
v_v_boxed_1686_ = lean_unbox(v_v_1685_);
v_res_1687_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_o_1683_, v_k_1684_, v_v_boxed_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(lean_object* v_opts_1688_, lean_object* v_opt_1689_, uint8_t v_val_1690_){
_start:
{
lean_object* v_name_1691_; lean_object* v___x_1692_; 
v_name_1691_ = lean_ctor_get(v_opt_1689_, 0);
lean_inc(v_name_1691_);
lean_dec_ref(v_opt_1689_);
v___x_1692_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_opts_1688_, v_name_1691_, v_val_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(lean_object* v_opts_1693_, lean_object* v_opt_1694_, lean_object* v_val_1695_){
_start:
{
uint8_t v_val_boxed_1696_; lean_object* v_res_1697_; 
v_val_boxed_1696_ = lean_unbox(v_val_1695_);
v_res_1697_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v_opts_1693_, v_opt_1694_, v_val_boxed_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(lean_object* v_msg_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_ref_1704_; lean_object* v___x_1705_; lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1714_; 
v_ref_1704_ = lean_ctor_get(v___y_1701_, 5);
v___x_1705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_inc(v_ref_1704_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_ref_1704_);
lean_ctor_set(v___x_1710_, 1, v_a_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_fileName_1733_; lean_object* v_fileMap_1734_; lean_object* v_options_1735_; lean_object* v_currRecDepth_1736_; lean_object* v_maxRecDepth_1737_; lean_object* v_ref_1738_; lean_object* v_currNamespace_1739_; lean_object* v_openDecls_1740_; lean_object* v_initHeartbeats_1741_; lean_object* v_maxHeartbeats_1742_; lean_object* v_quotContext_1743_; lean_object* v_currMacroScope_1744_; uint8_t v_diag_1745_; lean_object* v_cancelTk_x3f_1746_; uint8_t v_suppressElabErrors_1747_; lean_object* v_inheritedTraceOptions_1748_; lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_fileName_1733_ = lean_ctor_get(v___y_1730_, 0);
v_fileMap_1734_ = lean_ctor_get(v___y_1730_, 1);
v_options_1735_ = lean_ctor_get(v___y_1730_, 2);
v_currRecDepth_1736_ = lean_ctor_get(v___y_1730_, 3);
v_maxRecDepth_1737_ = lean_ctor_get(v___y_1730_, 4);
v_ref_1738_ = lean_ctor_get(v___y_1730_, 5);
v_currNamespace_1739_ = lean_ctor_get(v___y_1730_, 6);
v_openDecls_1740_ = lean_ctor_get(v___y_1730_, 7);
v_initHeartbeats_1741_ = lean_ctor_get(v___y_1730_, 8);
v_maxHeartbeats_1742_ = lean_ctor_get(v___y_1730_, 9);
v_quotContext_1743_ = lean_ctor_get(v___y_1730_, 10);
v_currMacroScope_1744_ = lean_ctor_get(v___y_1730_, 11);
v_diag_1745_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*14);
v_cancelTk_x3f_1746_ = lean_ctor_get(v___y_1730_, 12);
v_suppressElabErrors_1747_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1748_ = lean_ctor_get(v___y_1730_, 13);
v_ref_1749_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1738_);
lean_inc_ref(v_inheritedTraceOptions_1748_);
lean_inc(v_cancelTk_x3f_1746_);
lean_inc(v_currMacroScope_1744_);
lean_inc(v_quotContext_1743_);
lean_inc(v_maxHeartbeats_1742_);
lean_inc(v_initHeartbeats_1741_);
lean_inc(v_openDecls_1740_);
lean_inc(v_currNamespace_1739_);
lean_inc(v_maxRecDepth_1737_);
lean_inc(v_currRecDepth_1736_);
lean_inc_ref(v_options_1735_);
lean_inc_ref(v_fileMap_1734_);
lean_inc_ref(v_fileName_1733_);
v___x_1750_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1750_, 0, v_fileName_1733_);
lean_ctor_set(v___x_1750_, 1, v_fileMap_1734_);
lean_ctor_set(v___x_1750_, 2, v_options_1735_);
lean_ctor_set(v___x_1750_, 3, v_currRecDepth_1736_);
lean_ctor_set(v___x_1750_, 4, v_maxRecDepth_1737_);
lean_ctor_set(v___x_1750_, 5, v_ref_1749_);
lean_ctor_set(v___x_1750_, 6, v_currNamespace_1739_);
lean_ctor_set(v___x_1750_, 7, v_openDecls_1740_);
lean_ctor_set(v___x_1750_, 8, v_initHeartbeats_1741_);
lean_ctor_set(v___x_1750_, 9, v_maxHeartbeats_1742_);
lean_ctor_set(v___x_1750_, 10, v_quotContext_1743_);
lean_ctor_set(v___x_1750_, 11, v_currMacroScope_1744_);
lean_ctor_set(v___x_1750_, 12, v_cancelTk_x3f_1746_);
lean_ctor_set(v___x_1750_, 13, v_inheritedTraceOptions_1748_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14, v_diag_1745_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14 + 1, v_suppressElabErrors_1747_);
v___x_1751_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_1723_, v___y_1728_, v___y_1729_, v___x_1750_, v___y_1731_);
lean_dec_ref_known(v___x_1750_, 14);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg___boxed(lean_object* v_ref_1752_, lean_object* v_msg_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_1752_, v_msg_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v_ref_1752_);
return v_res_1763_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__0(void){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__1(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__0, &l_Lean_Elab_Tactic_evalImpossible___closed__0_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__0);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__2(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__1, &l_Lean_Elab_Tactic_evalImpossible___closed__1_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__1);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__3(void){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__4(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__3, &l_Lean_Elab_Tactic_evalImpossible___closed__3_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__3);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__5(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(32u);
v___x_1773_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__6(void){
_start:
{
size_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = ((size_t)5ULL);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_unsigned_to_nat(32u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
v___x_1779_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__5, &l_Lean_Elab_Tactic_evalImpossible___closed__5_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__5);
v___x_1780_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v___x_1778_);
lean_ctor_set(v___x_1780_, 2, v___x_1776_);
lean_ctor_set(v___x_1780_, 3, v___x_1776_);
lean_ctor_set_usize(v___x_1780_, 4, v___x_1775_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__7(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = lean_box(1);
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__6, &l_Lean_Elab_Tactic_evalImpossible___closed__6_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__6);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__4, &l_Lean_Elab_Tactic_evalImpossible___closed__4_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__4);
v___x_1784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1782_);
lean_ctor_set(v___x_1784_, 2, v___x_1781_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalImpossible___closed__12(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__11));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible(lean_object* v_stx_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v_a_1806_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; uint8_t v___y_1867_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = l_Lean_Syntax_getArg(v_stx_1793_, v___x_1831_);
v___x_1833_ = 0;
v___x_1889_ = 1;
v___x_1890_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(v___x_1832_, v___x_1833_, v___x_1889_, v_a_1794_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1795_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___f_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_n(v_a_1893_, 3);
lean_dec_ref_known(v___x_1892_, 1);
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1894_, 0, v_a_1893_);
v___x_1895_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_a_1893_, v___f_1894_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___f_1902_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___x_2019_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_unsigned_to_nat(2u);
v___x_1899_ = l_Lean_Syntax_getArg(v_stx_1793_, v___x_1898_);
v___x_1900_ = lean_unsigned_to_nat(3u);
v___x_1901_ = l_Lean_Syntax_getArg(v_stx_1793_, v___x_1900_);
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1902_, 0, v___x_1901_);
v___x_2019_ = l_Lean_Expr_hasLevelMVar(v_a_1896_);
if (v___x_2019_ == 0)
{
v___y_1904_ = v_a_1794_;
v___y_1905_ = v_a_1795_;
v___y_1906_ = v_a_1796_;
v___y_1907_ = v_a_1797_;
v___y_1908_ = v_a_1798_;
v___y_1909_ = v_a_1799_;
v___y_1910_ = v_a_1800_;
v___y_1911_ = v_a_1801_;
goto v___jp_1903_;
}
else
{
lean_object* v_kw_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
lean_dec(v_a_1893_);
lean_dec(v_a_1891_);
v_kw_2020_ = l_Lean_Syntax_getArg(v_stx_1793_, v___x_1897_);
v___x_2021_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__12, &l_Lean_Elab_Tactic_evalImpossible___closed__12_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__12);
v___x_2022_ = l_Lean_indentExpr(v_a_1896_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_kw_2020_, v___x_2023_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_kw_2020_);
return v___x_2024_;
}
v___jp_1903_:
{
uint8_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unbox(v_a_1891_);
lean_dec(v_a_1891_);
lean_inc(v_a_1893_);
v___x_1913_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(v_a_1893_, v_a_1896_, v___x_1912_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_2010_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v_fst_1915_ = lean_ctor_get(v_a_1914_, 0);
v_snd_1916_ = lean_ctor_get(v_a_1914_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_a_1914_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1918_ = v_a_1914_;
v_isShared_1919_ = v_isSharedCheck_2010_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_inc(v_fst_1915_);
lean_dec(v_a_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_2010_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Elab_admitGoal(v_a_1893_, v___x_1889_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; 
lean_dec_ref_known(v___x_1920_, 1);
v___x_1921_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__7, &l_Lean_Elab_Tactic_evalImpossible___closed__7_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__7);
v___x_1924_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__8));
v___x_1925_ = 2;
v___x_1926_ = lean_box(0);
lean_inc(v_fst_1915_);
v___x_1927_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1923_, v___x_1924_, v_fst_1915_, v___x_1925_, v___x_1926_, v___x_1897_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l_Lean_Expr_mvarId_x21(v_a_1928_);
lean_dec(v_a_1928_);
v___x_1930_ = lean_array_get_size(v_snd_1916_);
v___x_1931_ = lean_array_to_list(v_snd_1916_);
lean_inc(v___x_1929_);
v___x_1932_ = l_Lean_Meta_introNCore(v___x_1929_, v___x_1930_, v___x_1931_, v___x_1833_, v___x_1833_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_snd_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1984_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_snd_1934_ = lean_ctor_get(v_a_1933_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_a_1933_, 0);
lean_dec(v_unused_1985_);
v___x_1936_ = v_a_1933_;
v_isShared_1937_ = v_isSharedCheck_1984_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_snd_1934_);
lean_dec(v_a_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1984_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_box(0);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
lean_ctor_set(v___x_1936_, 1, v___x_1938_);
lean_ctor_set(v___x_1936_, 0, v_snd_1934_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_snd_1934_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_1940_, v___y_1905_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
lean_dec_ref_known(v___x_1941_, 1);
v___x_1942_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_1899_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed), 11, 1);
lean_closure_set(v___f_1944_, 0, v_a_1943_);
v___x_1945_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v___f_1902_, v___f_1944_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; 
lean_dec_ref_known(v___x_1945_, 1);
v___x_1946_ = l_Lean_mkMVar(v___x_1929_);
v___x_1947_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v___x_1946_, v___y_1909_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_fst_1915_, v___y_1909_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_a_1950_, v_a_1948_, v___x_1833_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1979_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = ((lean_object*)(l_Lean_Elab_Tactic_evalImpossible___closed__10));
v___x_1954_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v___x_1953_, v___y_1911_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_levelParams_1959_; lean_object* v_type_1960_; lean_object* v_value_1961_; lean_object* v___x_1962_; lean_object* v_options_1963_; lean_object* v_env_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v_levelParams_1959_ = lean_ctor_get(v_a_1952_, 0);
lean_inc_ref(v_levelParams_1959_);
v_type_1960_ = lean_ctor_get(v_a_1952_, 1);
lean_inc_ref(v_type_1960_);
v_value_1961_ = lean_ctor_get(v_a_1952_, 2);
lean_inc_ref(v_value_1961_);
lean_dec(v_a_1952_);
v___x_1962_ = lean_st_ref_get(v___y_1911_);
v_options_1963_ = lean_ctor_get(v___y_1910_, 2);
v_env_1964_ = lean_ctor_get(v___x_1962_, 0);
lean_inc_ref(v_env_1964_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_array_to_list(v_levelParams_1959_);
lean_inc(v_a_1955_);
v___x_1966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1955_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
lean_ctor_set(v___x_1966_, 2, v_type_1960_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 1);
lean_ctor_set(v___x_1918_, 1, v___x_1938_);
lean_ctor_set(v___x_1918_, 0, v_a_1955_);
v___x_1968_ = v___x_1918_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1955_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1938_);
v___x_1968_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1966_);
lean_ctor_set(v___x_1969_, 1, v_value_1961_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set_tag(v___x_1957_, 2);
lean_ctor_set(v___x_1957_, 0, v___x_1969_);
v___x_1971_ = v___x_1957_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1972_ = l_Lean_Elab_async;
lean_inc_ref(v_options_1963_);
v___x_1973_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(v_options_1963_, v___x_1972_, v___x_1833_);
v___x_1974_ = l_Lean_diagnostics;
v___x_1975_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_1973_, v___x_1974_);
v___x_1976_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1964_);
lean_dec_ref(v_env_1964_);
if (v___x_1976_ == 0)
{
if (v___x_1975_ == 0)
{
v___y_1860_ = v___x_1973_;
v___y_1861_ = v___y_1911_;
v___y_1862_ = v_a_1922_;
v___y_1863_ = v___y_1910_;
v___y_1864_ = v___x_1971_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___x_1975_;
v___y_1867_ = v___x_1889_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v___x_1973_;
v___y_1861_ = v___y_1911_;
v___y_1862_ = v_a_1922_;
v___y_1863_ = v___y_1910_;
v___y_1864_ = v___x_1971_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___x_1975_;
v___y_1867_ = v___x_1976_;
goto v___jp_1859_;
}
}
else
{
v___y_1860_ = v___x_1973_;
v___y_1861_ = v___y_1911_;
v___y_1862_ = v_a_1922_;
v___y_1863_ = v___y_1910_;
v___y_1864_ = v___x_1971_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___x_1975_;
v___y_1867_ = v___x_1975_;
goto v___jp_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1980_; 
lean_del_object(v___x_1918_);
v_a_1980_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1951_, 1);
v___y_1804_ = v_a_1922_;
v___y_1805_ = v___y_1905_;
v_a_1806_ = v_a_1980_;
goto v___jp_1803_;
}
}
else
{
lean_object* v_a_1981_; 
lean_dec(v___x_1929_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1915_);
v_a_1981_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1945_, 1);
v___y_1804_ = v_a_1922_;
v___y_1805_ = v___y_1905_;
v_a_1806_ = v_a_1981_;
goto v___jp_1803_;
}
}
else
{
lean_object* v_a_1982_; 
lean_dec(v___x_1929_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
v_a_1982_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1942_, 1);
v___y_1804_ = v_a_1922_;
v___y_1805_ = v___y_1905_;
v_a_1806_ = v_a_1982_;
goto v___jp_1803_;
}
}
else
{
lean_dec(v___x_1929_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
v___y_1817_ = v_a_1922_;
v___y_1818_ = v___y_1905_;
v___y_1819_ = v___x_1941_;
goto v___jp_1816_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v___x_1929_);
lean_dec(v_a_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
v_a_1986_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1932_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1932_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_snd_1916_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
v_a_1994_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1927_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1927_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_del_object(v___x_1918_);
lean_dec(v_snd_1916_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
v_a_2002_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1921_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1921_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_del_object(v___x_1918_);
lean_dec(v_snd_1916_);
lean_dec(v_fst_1915_);
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v___f_1902_);
lean_dec(v___x_1899_);
lean_dec(v_a_1893_);
v_a_2011_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1913_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1913_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1893_);
lean_dec(v_a_1891_);
v_a_2025_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1895_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1895_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_1891_);
v_a_2033_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1892_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1892_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_a_2041_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1890_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1890_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v___x_1807_, 0);
lean_dec(v_unused_1815_);
v___x_1809_ = v___x_1807_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v___x_1807_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 0, v_a_1806_);
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1806_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
else
{
lean_dec_ref(v_a_1806_);
return v___x_1807_;
}
}
v___jp_1816_:
{
if (lean_obj_tag(v___y_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___y_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___y_1819_, 1);
v___x_1821_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1821_, 0);
lean_dec(v_unused_1829_);
v___x_1823_ = v___x_1821_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___x_1821_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v_a_1820_);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1820_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_dec(v_a_1820_);
return v___x_1821_;
}
}
else
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___y_1819_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___y_1819_, 1);
v___y_1804_ = v___y_1817_;
v___y_1805_ = v___y_1818_;
v_a_1806_ = v_a_1830_;
goto v___jp_1803_;
}
}
v___jp_1834_:
{
lean_object* v_fileName_1842_; lean_object* v_fileMap_1843_; lean_object* v_currRecDepth_1844_; lean_object* v_ref_1845_; lean_object* v_currNamespace_1846_; lean_object* v_openDecls_1847_; lean_object* v_initHeartbeats_1848_; lean_object* v_maxHeartbeats_1849_; lean_object* v_quotContext_1850_; lean_object* v_currMacroScope_1851_; lean_object* v_cancelTk_x3f_1852_; uint8_t v_suppressElabErrors_1853_; lean_object* v_inheritedTraceOptions_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_fileName_1842_ = lean_ctor_get(v___y_1840_, 0);
v_fileMap_1843_ = lean_ctor_get(v___y_1840_, 1);
v_currRecDepth_1844_ = lean_ctor_get(v___y_1840_, 3);
v_ref_1845_ = lean_ctor_get(v___y_1840_, 5);
v_currNamespace_1846_ = lean_ctor_get(v___y_1840_, 6);
v_openDecls_1847_ = lean_ctor_get(v___y_1840_, 7);
v_initHeartbeats_1848_ = lean_ctor_get(v___y_1840_, 8);
v_maxHeartbeats_1849_ = lean_ctor_get(v___y_1840_, 9);
v_quotContext_1850_ = lean_ctor_get(v___y_1840_, 10);
v_currMacroScope_1851_ = lean_ctor_get(v___y_1840_, 11);
v_cancelTk_x3f_1852_ = lean_ctor_get(v___y_1840_, 12);
v_suppressElabErrors_1853_ = lean_ctor_get_uint8(v___y_1840_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1854_ = lean_ctor_get(v___y_1840_, 13);
v___x_1855_ = l_Lean_maxRecDepth;
v___x_1856_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(v___y_1835_, v___x_1855_);
lean_inc_ref(v_inheritedTraceOptions_1854_);
lean_inc(v_cancelTk_x3f_1852_);
lean_inc(v_currMacroScope_1851_);
lean_inc(v_quotContext_1850_);
lean_inc(v_maxHeartbeats_1849_);
lean_inc(v_initHeartbeats_1848_);
lean_inc(v_openDecls_1847_);
lean_inc(v_currNamespace_1846_);
lean_inc(v_ref_1845_);
lean_inc(v_currRecDepth_1844_);
lean_inc_ref(v_fileMap_1843_);
lean_inc_ref(v_fileName_1842_);
v___x_1857_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1857_, 0, v_fileName_1842_);
lean_ctor_set(v___x_1857_, 1, v_fileMap_1843_);
lean_ctor_set(v___x_1857_, 2, v___y_1835_);
lean_ctor_set(v___x_1857_, 3, v_currRecDepth_1844_);
lean_ctor_set(v___x_1857_, 4, v___x_1856_);
lean_ctor_set(v___x_1857_, 5, v_ref_1845_);
lean_ctor_set(v___x_1857_, 6, v_currNamespace_1846_);
lean_ctor_set(v___x_1857_, 7, v_openDecls_1847_);
lean_ctor_set(v___x_1857_, 8, v_initHeartbeats_1848_);
lean_ctor_set(v___x_1857_, 9, v_maxHeartbeats_1849_);
lean_ctor_set(v___x_1857_, 10, v_quotContext_1850_);
lean_ctor_set(v___x_1857_, 11, v_currMacroScope_1851_);
lean_ctor_set(v___x_1857_, 12, v_cancelTk_x3f_1852_);
lean_ctor_set(v___x_1857_, 13, v_inheritedTraceOptions_1854_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*14, v___y_1839_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*14 + 1, v_suppressElabErrors_1853_);
v___x_1858_ = l_Lean_addDecl(v___y_1837_, v___x_1833_, v___x_1857_, v___y_1841_);
lean_dec_ref_known(v___x_1857_, 14);
v___y_1817_ = v___y_1836_;
v___y_1818_ = v___y_1838_;
v___y_1819_ = v___x_1858_;
goto v___jp_1816_;
}
v___jp_1859_:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_bool_not(v___y_1867_);
if (v___x_1868_ == 0)
{
v___y_1835_ = v___y_1860_;
v___y_1836_ = v___y_1862_;
v___y_1837_ = v___y_1864_;
v___y_1838_ = v___y_1865_;
v___y_1839_ = v___y_1866_;
v___y_1840_ = v___y_1863_;
v___y_1841_ = v___y_1861_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_traceState_1874_; lean_object* v_messages_1875_; lean_object* v_infoState_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1887_; 
v___x_1869_ = lean_st_ref_take(v___y_1861_);
v_env_1870_ = lean_ctor_get(v___x_1869_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1869_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1869_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1869_, 3);
v_traceState_1874_ = lean_ctor_get(v___x_1869_, 4);
v_messages_1875_ = lean_ctor_get(v___x_1869_, 6);
v_infoState_1876_ = lean_ctor_get(v___x_1869_, 7);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1869_, 8);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1869_, 5);
lean_dec(v_unused_1888_);
v___x_1879_ = v___x_1869_;
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1876_);
lean_inc(v_messages_1875_);
lean_inc(v_traceState_1874_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1869_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = l_Lean_Kernel_enableDiag(v_env_1870_, v___y_1866_);
v___x_1882_ = lean_obj_once(&l_Lean_Elab_Tactic_evalImpossible___closed__2, &l_Lean_Elab_Tactic_evalImpossible___closed__2_once, _init_l_Lean_Elab_Tactic_evalImpossible___closed__2);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 5, v___x_1882_);
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_traceState_1874_);
lean_ctor_set(v_reuseFailAlloc_1886_, 5, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1886_, 6, v_messages_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 7, v_infoState_1876_);
lean_ctor_set(v_reuseFailAlloc_1886_, 8, v_snapshotTasks_1877_);
v___x_1884_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_st_ref_set(v___y_1861_, v___x_1884_);
v___y_1835_ = v___y_1860_;
v___y_1836_ = v___y_1862_;
v___y_1837_ = v___y_1864_;
v___y_1838_ = v___y_1865_;
v___y_1839_ = v___y_1866_;
v___y_1840_ = v___y_1863_;
v___y_1841_ = v___y_1861_;
goto v___jp_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalImpossible___boxed(lean_object* v_stx_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Elab_Tactic_evalImpossible(v_stx_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_stx_2049_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___boxed(lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(lean_object* v_00_u03b1_2080_, lean_object* v_x_2081_, lean_object* v_mkInfoTree_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v_x_2081_, v_mkInfoTree_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___boxed(lean_object* v_00_u03b1_2093_, lean_object* v_x_2094_, lean_object* v_mkInfoTree_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(v_00_u03b1_2093_, v_x_2094_, v_mkInfoTree_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(lean_object* v_00_u03b1_2106_, lean_object* v_ref_2107_, lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_ref_2107_, v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_ref_2120_, lean_object* v_msg_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(v_00_u03b1_2119_, v_ref_2120_, v_msg_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v_ref_2120_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(lean_object* v_00_u03b1_2132_, lean_object* v_msg_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_2133_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(v_00_u03b1_2144_, v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1(){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2170_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1));
v___x_2172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4));
v___x_2173_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalImpossible___boxed), 10, 0);
v___x_2174_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2170_, v___x_2171_, v___x_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___boxed(lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
return v_res_2176_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Impossible(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
