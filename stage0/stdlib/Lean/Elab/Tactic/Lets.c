// Lean compiler output
// Module: Lean.Elab.Tactic.Lets
// Imports: public import Lean.Meta.Tactic.Lets public import Lean.Elab.Tactic.Location import Lean.Elab.Binders import Lean.Linter.Init import Lean.Elab.ConfigEval
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_letToHave(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MVarId_extractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unusedName"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 206, 61, 199, 208, 244, 88, 253)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 220, 201, 55, 250, 95, 85, 187)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the 'unused name' tactic linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 218, 239, 141, 209, 224, 98, 123)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 199, 243, 68, 217, 216, 62, 142)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 222, 21, 214, 118, 132, 172, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_linter_tactic_unusedName;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unused name"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ExtractLetsConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "preserveBinderNames"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "underBinder"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "useContext"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "usedOnly"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(16, 226, 140, 93, 201, 161, 84, 201)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(211, 63, 87, 213, 28, 56, 122, 175)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 222, 109, 10, 158, 231, 13, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proofs"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(43, 83, 70, 124, 33, 60, 74, 155)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(215, 88, 172, 225, 56, 154, 23, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(144, 75, 207, 223, 242, 101, 87, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "merge"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "onlyGivenNames"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(11, 107, 77, 86, 119, 150, 185, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(58, 70, 65, 203, 53, 185, 57, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(222, 214, 80, 45, 206, 182, 252, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "descend"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "implicits"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(106, 15, 76, 87, 16, 201, 16, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(69, 112, 9, 105, 11, 83, 6, 15)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`extract_lets` tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 152, 152, 121, 17, 54, 202)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalExtractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 187, 108, 174, 23, 225, 147, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LiftLetsConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 138, 90, 221, 135, 228, 98, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`lift_lets` tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 154, 84, 113, 122, 200, 54, 62)}};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLiftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalLiftLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 204, 119, 233, 20, 201, 134, 20)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`let_to_have` tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 208, 147, 22, 140, 102, 111, 183)}};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalLetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 67, 243, 172, 71, 255, 176, 225)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_opts_64_, lean_object* v_opt_65_){
_start:
{
lean_object* v_name_66_; lean_object* v_defValue_67_; lean_object* v_map_68_; lean_object* v___x_69_; 
v_name_66_ = lean_ctor_get(v_opt_65_, 0);
v_defValue_67_ = lean_ctor_get(v_opt_65_, 1);
v_map_68_ = lean_ctor_get(v_opts_64_, 0);
v___x_69_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_68_, v_name_66_);
if (lean_obj_tag(v___x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = lean_unbox(v_defValue_67_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; 
v_val_71_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_71_);
lean_dec_ref_known(v___x_69_, 1);
if (lean_obj_tag(v_val_71_) == 1)
{
uint8_t v_v_72_; 
v_v_72_ = lean_ctor_get_uint8(v_val_71_, 0);
lean_dec_ref_known(v_val_71_, 0);
return v_v_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec(v_val_71_);
v___x_73_ = lean_unbox(v_defValue_67_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_74_, lean_object* v_opt_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_opts_74_, v_opt_75_);
lean_dec_ref(v_opt_75_);
lean_dec_ref(v_opts_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msgData_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; lean_object* v_env_85_; uint8_t v___x_86_; lean_object* v_env_87_; lean_object* v___x_88_; lean_object* v_toCold_89_; lean_object* v_mctx_90_; lean_object* v_lctx_91_; lean_object* v_options_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_84_ = lean_st_ref_get(v___y_82_);
v_env_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_84_);
v___x_86_ = 0;
v_env_87_ = l_Lean_Environment_setRecordingDeps(v_env_85_, v___x_86_);
v___x_88_ = lean_st_ref_get(v___y_80_);
v_toCold_89_ = lean_ctor_get(v___y_81_, 0);
v_mctx_90_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_mctx_90_);
lean_dec(v___x_88_);
v_lctx_91_ = lean_ctor_get(v___y_79_, 2);
v_options_92_ = lean_ctor_get(v_toCold_89_, 2);
lean_inc_ref(v_options_92_);
lean_inc_ref(v_lctx_91_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_env_87_);
lean_ctor_set(v___x_93_, 1, v_mctx_90_);
lean_ctor_set(v___x_93_, 2, v_lctx_91_);
lean_ctor_set(v___x_93_, 3, v_options_92_);
v___x_94_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v_msgData_78_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msgData_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msgData_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_pre_111_; 
v_pre_111_ = lean_ctor_get(v_x_110_, 0);
switch(lean_obj_tag(v_pre_111_))
{
case 1:
{
lean_object* v_pre_112_; 
v_pre_112_ = lean_ctor_get(v_pre_111_, 0);
switch(lean_obj_tag(v_pre_112_))
{
case 0:
{
lean_object* v_str_113_; lean_object* v_str_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_str_113_ = lean_ctor_get(v_x_110_, 1);
v_str_114_ = lean_ctor_get(v_pre_111_, 1);
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_116_ = lean_string_dec_eq(v_str_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_118_ = lean_string_dec_eq(v_str_114_, v___x_117_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_120_ = lean_string_dec_eq(v_str_113_, v___x_119_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
return v_suppressElabErrors_109_;
}
}
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_122_ = lean_string_dec_eq(v_str_113_, v___x_121_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
return v_suppressElabErrors_109_;
}
}
}
case 1:
{
lean_object* v_pre_123_; 
v_pre_123_ = lean_ctor_get(v_pre_112_, 0);
if (lean_obj_tag(v_pre_123_) == 0)
{
lean_object* v_str_124_; lean_object* v_str_125_; lean_object* v_str_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_str_124_ = lean_ctor_get(v_x_110_, 1);
v_str_125_ = lean_ctor_get(v_pre_111_, 1);
v_str_126_ = lean_ctor_get(v_pre_112_, 1);
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_128_ = lean_string_dec_eq(v_str_126_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_130_ = lean_string_dec_eq(v_str_125_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_132_ = lean_string_dec_eq(v_str_124_, v___x_131_);
if (v___x_132_ == 0)
{
return v___x_132_;
}
else
{
return v_suppressElabErrors_109_;
}
}
}
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
default: 
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
}
case 0:
{
lean_object* v_str_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_str_135_ = lean_ctor_get(v_x_110_, 1);
v___x_136_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_137_ = lean_string_dec_eq(v_str_135_, v___x_136_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
return v_suppressElabErrors_109_;
}
}
default: 
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
}
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_140_, lean_object* v_x_141_){
_start:
{
uint8_t v_suppressElabErrors_boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_suppressElabErrors_boxed_142_ = lean_unbox(v_suppressElabErrors_140_);
v_res_143_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_142_, v_x_141_);
lean_dec(v_x_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_146_, lean_object* v_msgData_147_, uint8_t v_severity_148_, uint8_t v_isSilent_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
uint8_t v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v_toCold_163_; lean_object* v___y_164_; lean_object* v___y_193_; lean_object* v___y_194_; uint8_t v___y_195_; uint8_t v___y_196_; lean_object* v___y_197_; uint8_t v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; uint8_t v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_230_; uint8_t v___y_231_; uint8_t v___x_241_; uint8_t v___y_243_; uint8_t v___x_249_; 
v___x_241_ = 2;
v___x_249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_241_);
if (v___x_249_ == 0)
{
v___y_243_ = v___x_249_;
goto v___jp_242_;
}
else
{
uint8_t v___x_250_; 
lean_inc_ref(v_msgData_147_);
v___x_250_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_147_);
if (v___x_250_ == 0)
{
v___y_243_ = v___x_250_;
goto v___jp_242_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v_msgData_147_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
v___jp_155_:
{
lean_object* v_currNamespace_165_; lean_object* v_openDecls_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_env_171_; lean_object* v_nextMacroScope_172_; lean_object* v_ngen_173_; lean_object* v_auxDeclNGen_174_; lean_object* v_traceState_175_; lean_object* v_cache_176_; lean_object* v_recordedDeps_177_; lean_object* v_messages_178_; lean_object* v_infoState_179_; lean_object* v_snapshotTasks_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_191_; 
v_currNamespace_165_ = lean_ctor_get(v_toCold_163_, 4);
v_openDecls_166_ = lean_ctor_get(v_toCold_163_, 5);
lean_inc(v_openDecls_166_);
lean_inc(v_currNamespace_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_currNamespace_165_);
lean_ctor_set(v___x_167_, 1, v_openDecls_166_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___y_159_);
lean_inc_ref(v___y_157_);
lean_inc_ref(v___y_161_);
v___x_169_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_169_, 0, v___y_161_);
lean_ctor_set(v___x_169_, 1, v___y_160_);
lean_ctor_set(v___x_169_, 2, v___y_162_);
lean_ctor_set(v___x_169_, 3, v___y_157_);
lean_ctor_set(v___x_169_, 4, v___x_168_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5, v___y_158_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 1, v___y_156_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 2, v_isSilent_149_);
v___x_170_ = lean_st_ref_take(v___y_164_);
v_env_171_ = lean_ctor_get(v___x_170_, 0);
v_nextMacroScope_172_ = lean_ctor_get(v___x_170_, 1);
v_ngen_173_ = lean_ctor_get(v___x_170_, 2);
v_auxDeclNGen_174_ = lean_ctor_get(v___x_170_, 3);
v_traceState_175_ = lean_ctor_get(v___x_170_, 4);
v_cache_176_ = lean_ctor_get(v___x_170_, 5);
v_recordedDeps_177_ = lean_ctor_get(v___x_170_, 6);
v_messages_178_ = lean_ctor_get(v___x_170_, 7);
v_infoState_179_ = lean_ctor_get(v___x_170_, 8);
v_snapshotTasks_180_ = lean_ctor_get(v___x_170_, 9);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_191_ == 0)
{
v___x_182_ = v___x_170_;
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_snapshotTasks_180_);
lean_inc(v_infoState_179_);
lean_inc(v_messages_178_);
lean_inc(v_recordedDeps_177_);
lean_inc(v_cache_176_);
lean_inc(v_traceState_175_);
lean_inc(v_auxDeclNGen_174_);
lean_inc(v_ngen_173_);
lean_inc(v_nextMacroScope_172_);
lean_inc(v_env_171_);
lean_dec(v___x_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_box(0);
v___x_185_ = l_Lean_MessageLog_add(v___x_169_, v_messages_178_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 7, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_env_171_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_nextMacroScope_172_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_ngen_173_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_auxDeclNGen_174_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_traceState_175_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_cache_176_);
lean_ctor_set(v_reuseFailAlloc_190_, 6, v_recordedDeps_177_);
lean_ctor_set(v_reuseFailAlloc_190_, 7, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_190_, 8, v_infoState_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 9, v_snapshotTasks_180_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_st_ref_put(v___y_164_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_184_);
return v___x_189_;
}
}
}
v___jp_192_:
{
lean_object* v_fileName_201_; lean_object* v_fileMap_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_218_; 
v_fileName_201_ = lean_ctor_get(v___y_199_, 0);
v_fileMap_202_ = lean_ctor_get(v___y_199_, 1);
v___x_203_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_147_);
v___x_204_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_203_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_218_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref_n(v_fileMap_202_, 2);
v___x_209_ = l_Lean_FileMap_toPosition(v_fileMap_202_, v___y_197_);
lean_dec(v___y_197_);
v___x_210_ = l_Lean_FileMap_toPosition(v_fileMap_202_, v___y_200_);
lean_dec(v___y_200_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_198_ == 0)
{
lean_del_object(v___x_207_);
lean_dec_ref(v___y_193_);
v___y_156_ = v___y_195_;
v___y_157_ = v___x_212_;
v___y_158_ = v___y_196_;
v___y_159_ = v_a_205_;
v___y_160_ = v___x_209_;
v___y_161_ = v_fileName_201_;
v___y_162_ = v___x_211_;
v_toCold_163_ = v___y_194_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
else
{
uint8_t v___x_213_; 
lean_inc(v_a_205_);
v___x_213_ = l_Lean_MessageData_hasTag(v___y_193_, v_a_205_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec_ref_known(v___x_211_, 1);
lean_dec_ref(v___x_209_);
lean_dec(v_a_205_);
v___x_214_ = lean_box(0);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_216_ = v___x_207_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
else
{
lean_del_object(v___x_207_);
v___y_156_ = v___y_195_;
v___y_157_ = v___x_212_;
v___y_158_ = v___y_196_;
v___y_159_ = v_a_205_;
v___y_160_ = v___x_209_;
v___y_161_ = v_fileName_201_;
v___y_162_ = v___x_211_;
v_toCold_163_ = v___y_194_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
}
}
}
v___jp_219_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Syntax_getTailPos_x3f(v___y_225_, v___y_224_);
lean_dec(v___y_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_inc(v___y_226_);
v___y_193_ = v___y_221_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_224_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_220_;
v___y_199_ = v___y_222_;
v___y_200_ = v___y_226_;
goto v___jp_192_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___y_193_ = v___y_221_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_224_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_220_;
v___y_199_ = v___y_222_;
v___y_200_ = v_val_228_;
goto v___jp_192_;
}
}
v___jp_229_:
{
lean_object* v_toCold_232_; lean_object* v_ref_233_; uint8_t v_suppressElabErrors_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v_ref_237_; lean_object* v___x_238_; 
v_toCold_232_ = lean_ctor_get(v___y_152_, 0);
v_ref_233_ = lean_ctor_get(v___y_152_, 2);
v_suppressElabErrors_234_ = lean_ctor_get_uint8(v___y_152_, sizeof(void*)*3 + 2);
v___x_235_ = lean_box(v_suppressElabErrors_234_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_236_, 0, v___x_235_);
v_ref_237_ = l_Lean_replaceRef(v_ref_146_, v_ref_233_);
v___x_238_ = l_Lean_Syntax_getPos_x3f(v_ref_237_, v___y_230_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___y_220_ = v_suppressElabErrors_234_;
v___y_221_ = v___f_236_;
v___y_222_ = v_toCold_232_;
v___y_223_ = v___y_231_;
v___y_224_ = v___y_230_;
v___y_225_ = v_ref_237_;
v___y_226_ = v___x_239_;
goto v___jp_219_;
}
else
{
lean_object* v_val_240_; 
v_val_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_238_, 1);
v___y_220_ = v_suppressElabErrors_234_;
v___y_221_ = v___f_236_;
v___y_222_ = v_toCold_232_;
v___y_223_ = v___y_231_;
v___y_224_ = v___y_230_;
v___y_225_ = v_ref_237_;
v___y_226_ = v_val_240_;
goto v___jp_219_;
}
}
v___jp_242_:
{
uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 1;
v___x_245_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_244_);
if (v___x_245_ == 0)
{
v___y_230_ = v___y_243_;
v___y_231_ = v_severity_148_;
goto v___jp_229_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_152_);
v___x_247_ = l_Lean_warningAsError;
v___x_248_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v___x_246_, v___x_247_);
lean_dec_ref(v___x_246_);
if (v___x_248_ == 0)
{
v___y_230_ = v___y_243_;
v___y_231_ = v_severity_148_;
goto v___jp_229_;
}
else
{
v___y_230_ = v___y_243_;
v___y_231_ = v___x_241_;
goto v___jp_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_253_, lean_object* v_msgData_254_, lean_object* v_severity_255_, lean_object* v_isSilent_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v_severity_boxed_262_; uint8_t v_isSilent_boxed_263_; lean_object* v_res_264_; 
v_severity_boxed_262_ = lean_unbox(v_severity_255_);
v_isSilent_boxed_263_ = lean_unbox(v_isSilent_256_);
v_res_264_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_253_, v_msgData_254_, v_severity_boxed_262_, v_isSilent_boxed_263_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v_ref_253_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object* v_ref_265_, lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = 1;
v___x_277_ = 0;
v___x_278_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_265_, v_msgData_266_, v___x_276_, v___x_277_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object* v_ref_279_, lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_279_, v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v_ref_279_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object* v_linterOption_297_, lean_object* v_stx_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_name_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_327_; 
v_name_309_ = lean_ctor_get(v_linterOption_297_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_linterOption_297_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_linterOption_297_, 1);
lean_dec(v_unused_328_);
v___x_311_ = v_linterOption_297_;
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_name_309_);
lean_dec(v_linterOption_297_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
lean_inc(v_name_309_);
v___x_314_ = l_Lean_MessageData_ofName(v_name_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 7);
lean_ctor_set(v___x_311_, 1, v___x_314_);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_326_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_disable_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_317_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v_disable_319_ = l_Lean_MessageData_note(v___x_318_);
v___x_320_ = l_Lean_Linter_linterMessageTag;
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v_msg_299_);
lean_ctor_set(v___x_321_, 1, v_disable_319_);
v___x_322_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_323_, 0, v_name_309_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v_stx_298_);
v___x_324_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_324_, 0, v_stx_298_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_298_, v___x_324_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v_stx_298_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object* v_linterOption_329_, lean_object* v_stx_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_329_, v_stx_330_, v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v___x_348_; lean_object* v_toEnvExtension_349_; lean_object* v_asyncMode_350_; lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v_merged_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_362_; 
v___x_345_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_346_ = lean_st_ref_get(v___y_343_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_349_ = lean_ctor_get(v___x_348_, 0);
v_asyncMode_350_ = lean_ctor_get(v_toEnvExtension_349_, 2);
v___x_351_ = lean_box(0);
v___x_352_ = 0;
v___x_353_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_345_, v___x_348_, v_env_347_, v_asyncMode_350_, v___x_351_, v___x_352_);
v_merged_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v___x_353_, 1);
lean_dec(v_unused_363_);
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_362_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_merged_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_362_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v_merged_354_);
lean_ctor_set(v___x_356_, 0, v_o_342_);
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_o_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_merged_354_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_364_, v___y_365_);
lean_dec(v___y_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_374_);
v___x_378_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v___x_377_, v___y_375_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_389_, lean_object* v_stx_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
v___x_401_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_412_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint8_t v___x_406_; 
v___x_406_ = l_Lean_Linter_getLinterValue(v_linterOption_389_, v_a_402_);
lean_dec(v_a_402_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec_ref(v_msg_391_);
lean_dec(v_stx_390_);
lean_dec_ref(v_linterOption_389_);
v___x_407_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v___x_411_; 
lean_del_object(v___x_404_);
v___x_411_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_389_, v_stx_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_413_, lean_object* v_stx_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_413_, v_stx_414_, v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_425_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_429_, lean_object* v_fvars_430_, lean_object* v_ids_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_a_444_; uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_lt(v_a_432_, v_upperBound_429_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_a_432_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_b_433_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_box(0);
v___x_451_ = lean_array_get_size(v_fvars_430_);
v___x_452_ = lean_nat_dec_lt(v_a_432_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_454_ = lean_array_fget_borrowed(v_ids_431_, v_a_432_);
v___x_455_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
lean_inc(v___x_454_);
v___x_456_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_453_, v___x_454_, v___x_455_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_dec_ref_known(v___x_456_, 1);
v_a_444_ = v___x_450_;
goto v___jp_443_;
}
else
{
lean_dec(v_a_432_);
return v___x_456_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_array_fget_borrowed(v_ids_431_, v_a_432_);
v___x_458_ = lean_array_fget_borrowed(v_fvars_430_, v_a_432_);
lean_inc(v___x_458_);
v___x_459_ = l_Lean_mkFVar(v___x_458_);
lean_inc(v___x_457_);
v___x_460_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_457_, v___x_459_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_dec_ref_known(v___x_460_, 1);
v_a_444_ = v___x_450_;
goto v___jp_443_;
}
else
{
lean_dec(v_a_432_);
return v___x_460_;
}
}
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_a_432_, v___x_445_);
lean_dec(v_a_432_);
v_a_432_ = v___x_446_;
v_b_433_ = v_a_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_461_, lean_object* v_fvars_462_, lean_object* v_ids_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_461_, v_fvars_462_, v_ids_463_, v_a_464_, v_b_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec_ref(v_ids_463_);
lean_dec_ref(v_fvars_462_);
lean_dec(v_upperBound_461_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_476_, lean_object* v_fvars_477_, lean_object* v_ids_478_, lean_object* v___x_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_476_, v_fvars_477_, v_ids_478_, v___x_489_, v___x_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_490_, 0);
lean_dec(v_unused_498_);
v___x_492_ = v___x_490_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_dec(v___x_490_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_479_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_479_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_499_, lean_object* v_fvars_500_, lean_object* v_ids_501_, lean_object* v___x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_499_, v_fvars_500_, v_ids_501_, v___x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_ids_501_);
lean_dec_ref(v_fvars_500_);
lean_dec(v___x_499_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_513_, lean_object* v_fvars_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v___x_524_ = lean_array_get_size(v_ids_513_);
v___x_525_ = lean_box(0);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_526_, 0, v___x_524_);
lean_closure_set(v___f_526_, 1, v_fvars_514_);
lean_closure_set(v___f_526_, 2, v_ids_513_);
lean_closure_set(v___f_526_, 3, v___x_525_);
v___x_527_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_526_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_528_, lean_object* v_fvars_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_528_, v_fvars_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_540_, lean_object* v_fvars_541_, lean_object* v_ids_542_, lean_object* v_inst_543_, lean_object* v_R_544_, lean_object* v_a_545_, lean_object* v_b_546_, lean_object* v_c_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_540_, v_fvars_541_, v_ids_542_, v_a_545_, v_b_546_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_558_ = _args[0];
lean_object* v_fvars_559_ = _args[1];
lean_object* v_ids_560_ = _args[2];
lean_object* v_inst_561_ = _args[3];
lean_object* v_R_562_ = _args[4];
lean_object* v_a_563_ = _args[5];
lean_object* v_b_564_ = _args[6];
lean_object* v_c_565_ = _args[7];
lean_object* v___y_566_ = _args[8];
lean_object* v___y_567_ = _args[9];
lean_object* v___y_568_ = _args[10];
lean_object* v___y_569_ = _args[11];
lean_object* v___y_570_ = _args[12];
lean_object* v___y_571_ = _args[13];
lean_object* v___y_572_ = _args[14];
lean_object* v___y_573_ = _args[15];
lean_object* v___y_574_ = _args[16];
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_558_, v_fvars_559_, v_ids_560_, v_inst_561_, v_R_562_, v_a_563_, v_b_564_, v_c_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_ids_560_);
lean_dec_ref(v_fvars_559_);
lean_dec(v_upperBound_558_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_576_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_598_, lean_object* v_msgData_599_, uint8_t v_severity_600_, uint8_t v_isSilent_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_598_, v_msgData_599_, v_severity_600_, v_isSilent_601_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_612_, lean_object* v_msgData_613_, lean_object* v_severity_614_, lean_object* v_isSilent_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
uint8_t v_severity_boxed_625_; uint8_t v_isSilent_boxed_626_; lean_object* v_res_627_; 
v_severity_boxed_625_ = lean_unbox(v_severity_614_);
v_isSilent_boxed_626_ = lean_unbox(v_isSilent_615_);
v_res_627_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_612_, v_msgData_613_, v_severity_boxed_625_, v_isSilent_boxed_626_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_ref_612_);
return v_res_627_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(lean_object* v_00_u03b1_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(v_00_u03b1_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_ref_656_ = lean_ctor_get(v___y_653_, 2);
v___x_657_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc(v_ref_656_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_ref_656_);
lean_ctor_set(v___x_662_, 1, v_a_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 1);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object* v___x_678_, lean_object* v_ctor_679_, lean_object* v_args_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_839_ = lean_string_dec_eq(v_ctor_679_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = lean_array_get_size(v_args_680_);
v___x_842_ = lean_unsigned_to_nat(11u);
v___x_843_ = lean_nat_dec_eq(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_845_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_844_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
goto v___jp_686_;
}
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_687_);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_688_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_691_);
lean_inc(v___x_692_);
v___x_693_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_692_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_unsigned_to_nat(2u);
v___x_696_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_695_);
lean_inc(v___x_696_);
v___x_697_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_696_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = lean_unsigned_to_nat(3u);
v___x_700_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_699_);
lean_inc(v___x_700_);
v___x_701_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_700_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_unsigned_to_nat(4u);
v___x_704_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_703_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_704_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_unsigned_to_nat(5u);
v___x_708_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_707_);
lean_inc(v___x_708_);
v___x_709_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_708_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_unsigned_to_nat(6u);
v___x_712_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_711_);
lean_inc(v___x_712_);
v___x_713_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_712_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = lean_unsigned_to_nat(7u);
v___x_716_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_715_);
lean_inc(v___x_716_);
v___x_717_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_716_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_unsigned_to_nat(8u);
v___x_720_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_719_);
lean_inc(v___x_720_);
v___x_721_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_720_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_unsigned_to_nat(9u);
v___x_724_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_723_);
lean_inc(v___x_724_);
v___x_725_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_724_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_unsigned_to_nat(10u);
v___x_728_ = lean_array_get_borrowed(v___x_678_, v_args_680_, v___x_727_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_728_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_749_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_749_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_749_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_749_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; uint8_t v___x_735_; uint8_t v___x_736_; uint8_t v___x_737_; uint8_t v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; lean_object* v___x_747_; 
v___x_734_ = lean_alloc_ctor(0, 0, 11);
v___x_735_ = lean_unbox(v_a_690_);
lean_dec(v_a_690_);
lean_ctor_set_uint8(v___x_734_, 0, v___x_735_);
v___x_736_ = lean_unbox(v_a_694_);
lean_dec(v_a_694_);
lean_ctor_set_uint8(v___x_734_, 1, v___x_736_);
v___x_737_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
lean_ctor_set_uint8(v___x_734_, 2, v___x_737_);
v___x_738_ = lean_unbox(v_a_702_);
lean_dec(v_a_702_);
lean_ctor_set_uint8(v___x_734_, 3, v___x_738_);
v___x_739_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
lean_ctor_set_uint8(v___x_734_, 4, v___x_739_);
v___x_740_ = lean_unbox(v_a_710_);
lean_dec(v_a_710_);
lean_ctor_set_uint8(v___x_734_, 5, v___x_740_);
v___x_741_ = lean_unbox(v_a_714_);
lean_dec(v_a_714_);
lean_ctor_set_uint8(v___x_734_, 6, v___x_741_);
v___x_742_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
lean_ctor_set_uint8(v___x_734_, 7, v___x_742_);
v___x_743_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
lean_ctor_set_uint8(v___x_734_, 8, v___x_743_);
v___x_744_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
lean_ctor_set_uint8(v___x_734_, 9, v___x_744_);
v___x_745_ = lean_unbox(v_a_730_);
lean_dec(v_a_730_);
lean_ctor_set_uint8(v___x_734_, 10, v___x_745_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_747_ = v___x_732_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_734_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_726_);
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_750_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_729_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_729_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_758_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_725_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_725_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_766_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_721_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_721_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_774_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_717_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_717_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_782_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_713_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_713_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_790_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_709_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_709_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_702_);
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_798_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_705_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_705_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_a_698_);
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_806_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_701_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_701_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_a_694_);
lean_dec(v_a_690_);
v_a_814_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_697_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_697_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_690_);
v_a_822_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_693_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_693_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_689_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_689_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object* v___x_854_, lean_object* v_ctor_855_, lean_object* v_args_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(v___x_854_, v_ctor_855_, v_args_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_args_856_);
lean_dec_ref(v_ctor_855_);
lean_dec_ref(v___x_854_);
return v_res_862_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_863_; lean_object* v___f_864_; 
v___x_863_ = l_Lean_instInhabitedExpr;
v___f_864_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_864_, 0, v___x_863_);
return v___f_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___f_877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0);
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_879_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_878_, v___f_877_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(lean_object* v_00_u03b1_887_, lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(v_00_u03b1_895_, v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(0);
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_906_ = l_Lean_Expr_const___override(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0));
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_913_, lean_object* v___y_914_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Expr_hasMVar(v_e_913_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_e_913_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v_mctx_919_; lean_object* v___x_920_; lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_923_; lean_object* v_cache_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_936_; 
v___x_918_ = lean_st_ref_get(v___y_914_);
v_mctx_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_mctx_919_);
lean_dec(v___x_918_);
v___x_920_ = l_Lean_instantiateMVarsCore(v_mctx_919_, v_e_913_);
v_fst_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_fst_921_);
v_snd_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_snd_922_);
lean_dec_ref(v___x_920_);
v___x_923_ = lean_st_ref_take(v___y_914_);
v_cache_924_ = lean_ctor_get(v___x_923_, 1);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_923_, 2);
v_postponed_926_ = lean_ctor_get(v___x_923_, 3);
v_diag_927_ = lean_ctor_get(v___x_923_, 4);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_937_);
v___x_929_ = v___x_923_;
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_diag_927_);
lean_inc(v_postponed_926_);
lean_inc(v_zetaDeltaFVarIds_925_);
lean_inc(v_cache_924_);
lean_dec(v___x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v_snd_922_);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_snd_922_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_diag_927_);
v___x_932_ = v_reuseFailAlloc_935_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_st_ref_put(v___y_914_, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_fst_921_);
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_938_, v___y_939_);
lean_dec(v___y_939_);
return v_res_941_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_box(1);
v___x_943_ = l_Lean_MessageData_ofFormat(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2));
v___x_948_ = l_Lean_MessageData_ofFormat(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
if (lean_obj_tag(v_x_950_) == 0)
{
return v_x_949_;
}
else
{
lean_object* v_head_951_; lean_object* v_tail_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_974_; 
v_head_951_ = lean_ctor_get(v_x_950_, 0);
v_tail_952_ = lean_ctor_get(v_x_950_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_950_);
if (v_isSharedCheck_974_ == 0)
{
v___x_954_ = v_x_950_;
v_isShared_955_ = v_isSharedCheck_974_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_tail_952_);
lean_inc(v_head_951_);
lean_dec(v_x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_974_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_before_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_972_; 
v_before_956_ = lean_ctor_get(v_head_951_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_head_951_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_head_951_, 1);
lean_dec(v_unused_973_);
v___x_958_ = v_head_951_;
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_before_956_);
lean_dec(v_head_951_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 7);
lean_ctor_set(v___x_958_, 1, v___x_960_);
lean_ctor_set(v___x_958_, 0, v_x_949_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_x_949_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_971_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 7);
lean_ctor_set(v___x_954_, 1, v___x_963_);
lean_ctor_set(v___x_954_, 0, v___x_962_);
v___x_965_ = v___x_954_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_970_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_MessageData_ofSyntax(v_before_956_);
v___x_967_ = l_Lean_indentD(v___x_966_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v_x_949_ = v___x_968_;
v_x_950_ = v_tail_952_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_979_ = l_Lean_MessageData_ofFormat(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_980_, lean_object* v_macroStack_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_982_);
v___x_985_ = l_Lean_Elab_pp_macroStack;
v___x_986_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v___x_984_, v___x_985_);
lean_dec_ref(v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v_macroStack_981_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_msgData_980_);
return v___x_987_;
}
else
{
if (lean_obj_tag(v_macroStack_981_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_msgData_980_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_after_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1005_; 
v_head_989_ = lean_ctor_get(v_macroStack_981_, 0);
lean_inc(v_head_989_);
v_after_990_ = lean_ctor_get(v_head_989_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_head_989_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v_head_989_, 0);
lean_dec(v_unused_1006_);
v___x_992_ = v_head_989_;
v_isShared_993_ = v_isSharedCheck_1005_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_after_990_);
lean_dec(v_head_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1005_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 7);
lean_ctor_set(v___x_992_, 1, v___x_994_);
lean_ctor_set(v___x_992_, 0, v_msgData_980_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_msgData_980_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1004_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_msgData_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_997_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_MessageData_ofSyntax(v_after_990_);
v___x_1000_ = l_Lean_indentD(v___x_999_);
v_msgData_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1001_, 0, v___x_998_);
lean_ctor_set(v_msgData_1001_, 1, v___x_1000_);
v___x_1002_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_msgData_1001_, v_macroStack_981_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1007_, lean_object* v_macroStack_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1007_, v_macroStack_1008_, v___y_1009_);
lean_dec_ref(v___y_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_ref_1020_; lean_object* v_macroStack_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_ref_1020_ = lean_ctor_get(v___y_1017_, 2);
v_macroStack_1021_ = lean_ctor_get(v___y_1013_, 1);
v___x_1022_ = l_Lean_Elab_getBetterRef(v_ref_1020_, v_macroStack_1021_);
v___x_1023_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1012_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
lean_inc(v_macroStack_1021_);
v___x_1025_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_1024_, v_macroStack_1021_, v___y_1017_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1022_);
lean_ctor_set(v___x_1030_, 1, v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1043_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Lean_Elab_abortTermExceptionId;
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_1056_ = l_Lean_MessageData_ofExpr(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_1058_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_1064_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_ty_x3f_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_toCold_1086_; lean_object* v_currRecDepth_1087_; lean_object* v_ref_1088_; uint16_t v_optionFlags_1089_; uint8_t v_suppressElabErrors_1090_; uint8_t v_isRecordingDeps_1091_; uint8_t v___x_1092_; lean_object* v_ref_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_ty_x3f_1080_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_1081_ = 1;
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_box(v___x_1081_);
v___x_1084_ = lean_box(v___x_1081_);
lean_inc(v_stx_1072_);
v___x_1085_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1085_, 0, v_stx_1072_);
lean_closure_set(v___x_1085_, 1, v_ty_x3f_1080_);
lean_closure_set(v___x_1085_, 2, v___x_1083_);
lean_closure_set(v___x_1085_, 3, v___x_1084_);
lean_closure_set(v___x_1085_, 4, v___x_1082_);
v_toCold_1086_ = lean_ctor_get(v_a_1077_, 0);
v_currRecDepth_1087_ = lean_ctor_get(v_a_1077_, 1);
v_ref_1088_ = lean_ctor_get(v_a_1077_, 2);
v_optionFlags_1089_ = lean_ctor_get_uint16(v_a_1077_, sizeof(void*)*3);
v_suppressElabErrors_1090_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1091_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*3 + 3);
v___x_1092_ = 1;
v_ref_1093_ = l_Lean_replaceRef(v_stx_1072_, v_ref_1088_);
lean_dec(v_stx_1072_);
lean_inc(v_currRecDepth_1087_);
lean_inc_ref(v_toCold_1086_);
v___x_1094_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1094_, 0, v_toCold_1086_);
lean_ctor_set(v___x_1094_, 1, v_currRecDepth_1087_);
lean_ctor_set(v___x_1094_, 2, v_ref_1093_);
lean_ctor_set_uint16(v___x_1094_, sizeof(void*)*3, v_optionFlags_1089_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 2, v_suppressElabErrors_1090_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 3, v_isRecordingDeps_1091_);
v___x_1095_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1085_, v___x_1092_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v___x_1094_, v_a_1078_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v_a_1098_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; uint8_t v___x_1182_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_1096_, v_a_1076_);
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1097_);
v___x_1182_ = l_Lean_Expr_hasSorry(v_a_1098_);
if (v___x_1182_ == 0)
{
v___y_1127_ = v_a_1073_;
v___y_1128_ = v_a_1074_;
v___y_1129_ = v_a_1075_;
v___y_1130_ = v_a_1076_;
v___y_1131_ = v___x_1094_;
v___y_1132_ = v_a_1078_;
goto v___jp_1126_;
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Lean_Expr_hasSyntheticSorry(v_a_1098_);
if (v___x_1183_ == 0)
{
v___y_1164_ = v_a_1073_;
v___y_1165_ = v_a_1074_;
v___y_1166_ = v_a_1075_;
v___y_1167_ = v_a_1076_;
v___y_1168_ = v___x_1094_;
v___y_1169_ = v_a_1078_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1184_; lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1098_);
lean_dec_ref_known(v___x_1094_, 3);
v___x_1184_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
v___jp_1099_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1098_);
v___x_1107_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_1098_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1098_);
return v___x_1107_;
}
else
{
lean_object* v_a_1108_; uint8_t v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
v___x_1109_ = l_Lean_Exception_isInterrupt(v_a_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; 
lean_inc(v_a_1108_);
v___x_1110_ = l_Lean_Exception_isRuntime(v_a_1108_);
if (v___x_1110_ == 0)
{
if (lean_obj_tag(v_a_1108_) == 0)
{
lean_dec_ref_known(v_a_1108_, 2);
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1098_);
return v___x_1107_;
}
else
{
lean_object* v_id_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1124_; 
v_id_1111_ = lean_ctor_get(v_a_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_a_1108_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_a_1108_, 1);
lean_dec(v_unused_1125_);
v___x_1113_ = v_a_1108_;
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_id_1111_);
lean_dec(v_a_1108_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1106_, v_id_1111_);
lean_dec(v_id_1111_);
if (v___x_1115_ == 0)
{
lean_del_object(v___x_1113_);
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1098_);
return v___x_1107_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref_known(v___x_1107_, 1);
v___x_1116_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6);
v___x_1117_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_1118_ = l_Lean_indentExpr(v_a_1098_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 7);
lean_ctor_set(v___x_1113_, 1, v___x_1118_);
lean_ctor_set(v___x_1113_, 0, v___x_1117_);
v___x_1120_ = v___x_1113_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___x_1116_);
v___x_1122_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1121_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v___y_1104_);
return v___x_1122_;
}
}
}
}
}
else
{
lean_dec(v_a_1108_);
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1098_);
return v___x_1107_;
}
}
else
{
lean_dec(v_a_1108_);
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1098_);
return v___x_1107_;
}
}
}
v___jp_1126_:
{
lean_object* v___x_1133_; 
lean_inc(v_a_1098_);
v___x_1133_ = l_Lean_Meta_getMVars(v_a_1098_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1134_, v___x_1082_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v_a_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; uint8_t v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = lean_unbox(v_a_1136_);
lean_dec(v_a_1136_);
if (v___x_1137_ == 0)
{
v___y_1100_ = v___y_1127_;
v___y_1101_ = v___y_1128_;
v___y_1102_ = v___y_1129_;
v___y_1103_ = v___y_1130_;
v___y_1104_ = v___y_1131_;
v___y_1105_ = v___y_1132_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1138_; lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___y_1131_);
lean_dec(v_a_1098_);
v___x_1138_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v___y_1131_);
lean_dec(v_a_1098_);
v_a_1147_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1135_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1135_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___y_1131_);
lean_dec(v_a_1098_);
v_a_1155_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1133_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1133_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
v___jp_1163_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v___x_1170_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_1171_ = l_Lean_indentExpr(v_a_1098_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1172_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec_ref(v___y_1168_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref_known(v___x_1094_, 3);
v_a_1193_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1095_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1095_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_stx_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(lean_object* v_config_1279_, lean_object* v_item_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_item_1289_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1293_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1280_, v___x_1292_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1293_) == 0)
{
uint8_t v___x_1294_; 
lean_dec_ref_known(v___x_1293_, 1);
v___x_1294_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1280_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1295_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1280_);
lean_inc_ref(v_item_1280_);
v___x_1296_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1280_);
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_1298_ = lean_string_dec_lt(v___x_1295_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_1300_ = lean_string_dec_lt(v___x_1295_, v___x_1299_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_string_dec_eq(v___x_1295_, v___x_1299_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_1303_ = lean_string_dec_eq(v___x_1295_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_1305_ = lean_string_dec_eq(v___x_1295_, v___x_1304_);
lean_dec_ref(v___x_1295_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_1307_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1306_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1307_) == 0)
{
uint8_t v___x_1308_; 
lean_dec_ref_known(v___x_1307_, 1);
v___x_1308_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v___x_1296_);
v___x_1309_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1335_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
uint8_t v_proofs_1314_; uint8_t v_types_1315_; uint8_t v_implicits_1316_; uint8_t v_descend_1317_; uint8_t v_underBinder_1318_; uint8_t v_merge_1319_; uint8_t v_useContext_1320_; uint8_t v_onlyGivenNames_1321_; uint8_t v_preserveBinderNames_1322_; uint8_t v_lift_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1334_; 
v_proofs_1314_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1315_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1316_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1317_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1318_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_merge_1319_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1320_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1321_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1322_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1323_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1325_ = v_config_1279_;
v_isShared_1326_ = v_isSharedCheck_1334_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_config_1279_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1334_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 0, v_proofs_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 1, v_types_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 2, v_implicits_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 3, v_descend_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 4, v_underBinder_1318_);
v___x_1328_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
uint8_t v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
lean_ctor_set_uint8(v___x_1328_, 5, v___x_1329_);
lean_ctor_set_uint8(v___x_1328_, 6, v_merge_1319_);
lean_ctor_set_uint8(v___x_1328_, 7, v_useContext_1320_);
lean_ctor_set_uint8(v___x_1328_, 8, v_onlyGivenNames_1321_);
lean_ctor_set_uint8(v___x_1328_, 9, v_preserveBinderNames_1322_);
lean_ctor_set_uint8(v___x_1328_, 10, v_lift_1323_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1328_);
v___x_1331_ = v___x_1312_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1328_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_config_1279_);
v_a_1336_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1309_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1309_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1344_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1307_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1307_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v___x_1295_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_1353_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1352_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1353_) == 0)
{
uint8_t v___x_1354_; 
lean_dec_ref_known(v___x_1353_, 1);
v___x_1354_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1355_; 
lean_dec_ref(v___x_1296_);
v___x_1355_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1381_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1381_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1381_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v_proofs_1360_; uint8_t v_types_1361_; uint8_t v_implicits_1362_; uint8_t v_descend_1363_; uint8_t v_underBinder_1364_; uint8_t v_usedOnly_1365_; uint8_t v_merge_1366_; uint8_t v_onlyGivenNames_1367_; uint8_t v_preserveBinderNames_1368_; uint8_t v_lift_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1380_; 
v_proofs_1360_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1361_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1362_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1363_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1364_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1365_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1366_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_onlyGivenNames_1367_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1368_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1369_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1371_ = v_config_1279_;
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_config_1279_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 0, v_proofs_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 1, v_types_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 2, v_implicits_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 3, v_descend_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 4, v_underBinder_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 5, v_usedOnly_1365_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 6, v_merge_1366_);
v___x_1374_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
uint8_t v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unbox(v_a_1356_);
lean_dec(v_a_1356_);
lean_ctor_set_uint8(v___x_1374_, 7, v___x_1375_);
lean_ctor_set_uint8(v___x_1374_, 8, v_onlyGivenNames_1367_);
lean_ctor_set_uint8(v___x_1374_, 9, v_preserveBinderNames_1368_);
lean_ctor_set_uint8(v___x_1374_, 10, v_lift_1369_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1374_);
v___x_1377_ = v___x_1358_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_config_1279_);
v_a_1382_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1355_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1355_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1390_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1353_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1353_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v___x_1295_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_1399_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1398_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1399_) == 0)
{
uint8_t v___x_1400_; 
lean_dec_ref_known(v___x_1399_, 1);
v___x_1400_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v___x_1296_);
v___x_1401_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1427_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1427_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1427_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v_proofs_1406_; uint8_t v_types_1407_; uint8_t v_implicits_1408_; uint8_t v_descend_1409_; uint8_t v_usedOnly_1410_; uint8_t v_merge_1411_; uint8_t v_useContext_1412_; uint8_t v_onlyGivenNames_1413_; uint8_t v_preserveBinderNames_1414_; uint8_t v_lift_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1426_; 
v_proofs_1406_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1407_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1408_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1409_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_usedOnly_1410_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1411_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1412_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1413_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1414_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1415_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1417_ = v_config_1279_;
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v_config_1279_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, 0, v_proofs_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, 1, v_types_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, 2, v_implicits_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, 3, v_descend_1409_);
v___x_1420_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
uint8_t v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_unbox(v_a_1402_);
lean_dec(v_a_1402_);
lean_ctor_set_uint8(v___x_1420_, 4, v___x_1421_);
lean_ctor_set_uint8(v___x_1420_, 5, v_usedOnly_1410_);
lean_ctor_set_uint8(v___x_1420_, 6, v_merge_1411_);
lean_ctor_set_uint8(v___x_1420_, 7, v_useContext_1412_);
lean_ctor_set_uint8(v___x_1420_, 8, v_onlyGivenNames_1413_);
lean_ctor_set_uint8(v___x_1420_, 9, v_preserveBinderNames_1414_);
lean_ctor_set_uint8(v___x_1420_, 10, v_lift_1415_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1420_);
v___x_1423_ = v___x_1404_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1420_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_config_1279_);
v_a_1428_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1401_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1401_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1436_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1399_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1399_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_string_dec_eq(v___x_1295_, v___x_1297_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_1446_ = lean_string_dec_eq(v___x_1295_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_1448_ = lean_string_dec_eq(v___x_1295_, v___x_1447_);
lean_dec_ref(v___x_1295_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_1450_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1449_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1450_) == 0)
{
uint8_t v___x_1451_; 
lean_dec_ref_known(v___x_1450_, 1);
v___x_1451_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1451_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1452_; 
lean_dec_ref(v___x_1296_);
v___x_1452_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1478_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1478_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1478_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v_proofs_1457_; uint8_t v_implicits_1458_; uint8_t v_descend_1459_; uint8_t v_underBinder_1460_; uint8_t v_usedOnly_1461_; uint8_t v_merge_1462_; uint8_t v_useContext_1463_; uint8_t v_onlyGivenNames_1464_; uint8_t v_preserveBinderNames_1465_; uint8_t v_lift_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1477_; 
v_proofs_1457_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_implicits_1458_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1459_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1460_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1461_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1462_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1463_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1464_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1465_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1466_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1468_ = v_config_1279_;
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_config_1279_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, 0, v_proofs_1457_);
v___x_1471_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
uint8_t v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unbox(v_a_1453_);
lean_dec(v_a_1453_);
lean_ctor_set_uint8(v___x_1471_, 1, v___x_1472_);
lean_ctor_set_uint8(v___x_1471_, 2, v_implicits_1458_);
lean_ctor_set_uint8(v___x_1471_, 3, v_descend_1459_);
lean_ctor_set_uint8(v___x_1471_, 4, v_underBinder_1460_);
lean_ctor_set_uint8(v___x_1471_, 5, v_usedOnly_1461_);
lean_ctor_set_uint8(v___x_1471_, 6, v_merge_1462_);
lean_ctor_set_uint8(v___x_1471_, 7, v_useContext_1463_);
lean_ctor_set_uint8(v___x_1471_, 8, v_onlyGivenNames_1464_);
lean_ctor_set_uint8(v___x_1471_, 9, v_preserveBinderNames_1465_);
lean_ctor_set_uint8(v___x_1471_, 10, v_lift_1466_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1471_);
v___x_1474_ = v___x_1455_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1471_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_config_1279_);
v_a_1479_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1452_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1452_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1487_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1450_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1450_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___x_1295_);
v___x_1495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_1496_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1495_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1496_) == 0)
{
uint8_t v___x_1497_; 
lean_dec_ref_known(v___x_1496_, 1);
v___x_1497_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1497_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1498_; 
lean_dec_ref(v___x_1296_);
v___x_1498_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1524_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1524_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1524_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint8_t v_types_1503_; uint8_t v_implicits_1504_; uint8_t v_descend_1505_; uint8_t v_underBinder_1506_; uint8_t v_usedOnly_1507_; uint8_t v_merge_1508_; uint8_t v_useContext_1509_; uint8_t v_onlyGivenNames_1510_; uint8_t v_preserveBinderNames_1511_; uint8_t v_lift_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1523_; 
v_types_1503_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1504_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1505_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1506_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1507_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1508_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1509_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1510_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1511_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1512_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1514_ = v_config_1279_;
v_isShared_1515_ = v_isSharedCheck_1523_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_config_1279_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1523_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 0, 11);
v___x_1517_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
uint8_t v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_unbox(v_a_1499_);
lean_dec(v_a_1499_);
lean_ctor_set_uint8(v___x_1517_, 0, v___x_1518_);
lean_ctor_set_uint8(v___x_1517_, 1, v_types_1503_);
lean_ctor_set_uint8(v___x_1517_, 2, v_implicits_1504_);
lean_ctor_set_uint8(v___x_1517_, 3, v_descend_1505_);
lean_ctor_set_uint8(v___x_1517_, 4, v_underBinder_1506_);
lean_ctor_set_uint8(v___x_1517_, 5, v_usedOnly_1507_);
lean_ctor_set_uint8(v___x_1517_, 6, v_merge_1508_);
lean_ctor_set_uint8(v___x_1517_, 7, v_useContext_1509_);
lean_ctor_set_uint8(v___x_1517_, 8, v_onlyGivenNames_1510_);
lean_ctor_set_uint8(v___x_1517_, 9, v_preserveBinderNames_1511_);
lean_ctor_set_uint8(v___x_1517_, 10, v_lift_1512_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1517_);
v___x_1520_ = v___x_1501_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1517_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v_config_1279_);
v_a_1525_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1498_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1498_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1533_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1496_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1496_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec_ref(v___x_1295_);
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_1542_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1541_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1542_) == 0)
{
uint8_t v___x_1543_; 
lean_dec_ref_known(v___x_1542_, 1);
v___x_1543_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1543_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1544_; 
lean_dec_ref(v___x_1296_);
v___x_1544_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1570_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1570_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1570_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v_proofs_1549_; uint8_t v_types_1550_; uint8_t v_implicits_1551_; uint8_t v_descend_1552_; uint8_t v_underBinder_1553_; uint8_t v_usedOnly_1554_; uint8_t v_merge_1555_; uint8_t v_useContext_1556_; uint8_t v_onlyGivenNames_1557_; uint8_t v_lift_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1569_; 
v_proofs_1549_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1550_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1551_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1552_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1553_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1554_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1555_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1556_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1557_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_lift_1558_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1560_ = v_config_1279_;
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v_config_1279_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 0, v_proofs_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 1, v_types_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 2, v_implicits_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 3, v_descend_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 4, v_underBinder_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 5, v_usedOnly_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 6, v_merge_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 7, v_useContext_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, 8, v_onlyGivenNames_1557_);
v___x_1563_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
uint8_t v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
lean_ctor_set_uint8(v___x_1563_, 9, v___x_1564_);
lean_ctor_set_uint8(v___x_1563_, 10, v_lift_1558_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1563_);
v___x_1566_ = v___x_1547_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1563_);
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
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_config_1279_);
v_a_1571_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1544_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1544_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1579_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1542_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1542_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
else
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_1588_ = lean_string_dec_lt(v___x_1295_, v___x_1587_);
if (v___x_1588_ == 0)
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_string_dec_eq(v___x_1295_, v___x_1587_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_1591_ = lean_string_dec_eq(v___x_1295_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_1593_ = lean_string_dec_eq(v___x_1295_, v___x_1592_);
lean_dec_ref(v___x_1295_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_1595_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1594_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1595_) == 0)
{
uint8_t v___x_1596_; 
lean_dec_ref_known(v___x_1595_, 1);
v___x_1596_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1596_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1597_; 
lean_dec_ref(v___x_1296_);
v___x_1597_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1623_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1623_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1623_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint8_t v_proofs_1602_; uint8_t v_types_1603_; uint8_t v_implicits_1604_; uint8_t v_descend_1605_; uint8_t v_underBinder_1606_; uint8_t v_usedOnly_1607_; uint8_t v_merge_1608_; uint8_t v_useContext_1609_; uint8_t v_preserveBinderNames_1610_; uint8_t v_lift_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1622_; 
v_proofs_1602_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1603_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1604_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1605_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1606_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1607_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1608_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1609_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_preserveBinderNames_1610_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1611_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1613_ = v_config_1279_;
v_isShared_1614_ = v_isSharedCheck_1622_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v_config_1279_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1622_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 0, v_proofs_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 1, v_types_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 2, v_implicits_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 3, v_descend_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 4, v_underBinder_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 5, v_usedOnly_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 6, v_merge_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, 7, v_useContext_1609_);
v___x_1616_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
uint8_t v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_unbox(v_a_1598_);
lean_dec(v_a_1598_);
lean_ctor_set_uint8(v___x_1616_, 8, v___x_1617_);
lean_ctor_set_uint8(v___x_1616_, 9, v_preserveBinderNames_1610_);
lean_ctor_set_uint8(v___x_1616_, 10, v_lift_1611_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1616_);
v___x_1619_ = v___x_1600_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_config_1279_);
v_a_1624_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1597_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1597_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1632_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1595_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1595_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v___x_1295_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_1641_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1640_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1641_) == 0)
{
uint8_t v___x_1642_; 
lean_dec_ref_known(v___x_1641_, 1);
v___x_1642_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1643_; 
lean_dec_ref(v___x_1296_);
v___x_1643_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1669_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1669_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1669_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v_proofs_1648_; uint8_t v_types_1649_; uint8_t v_implicits_1650_; uint8_t v_descend_1651_; uint8_t v_underBinder_1652_; uint8_t v_usedOnly_1653_; uint8_t v_useContext_1654_; uint8_t v_onlyGivenNames_1655_; uint8_t v_preserveBinderNames_1656_; uint8_t v_lift_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1668_; 
v_proofs_1648_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1649_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1650_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1651_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1652_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1653_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_useContext_1654_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1655_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1656_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1657_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1659_ = v_config_1279_;
v_isShared_1660_ = v_isSharedCheck_1668_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v_config_1279_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1668_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 0, v_proofs_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 1, v_types_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 2, v_implicits_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 3, v_descend_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 4, v_underBinder_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, 5, v_usedOnly_1653_);
v___x_1662_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
uint8_t v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unbox(v_a_1644_);
lean_dec(v_a_1644_);
lean_ctor_set_uint8(v___x_1662_, 6, v___x_1663_);
lean_ctor_set_uint8(v___x_1662_, 7, v_useContext_1654_);
lean_ctor_set_uint8(v___x_1662_, 8, v_onlyGivenNames_1655_);
lean_ctor_set_uint8(v___x_1662_, 9, v_preserveBinderNames_1656_);
lean_ctor_set_uint8(v___x_1662_, 10, v_lift_1657_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1662_);
v___x_1665_ = v___x_1646_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1662_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_config_1279_);
v_a_1670_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1643_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1643_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
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
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1678_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1641_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1641_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref(v___x_1295_);
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_1687_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1686_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1687_) == 0)
{
uint8_t v___x_1688_; 
lean_dec_ref_known(v___x_1687_, 1);
v___x_1688_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1689_; 
lean_dec_ref(v___x_1296_);
v___x_1689_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1715_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1715_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1715_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v_proofs_1694_; uint8_t v_types_1695_; uint8_t v_implicits_1696_; uint8_t v_descend_1697_; uint8_t v_underBinder_1698_; uint8_t v_usedOnly_1699_; uint8_t v_merge_1700_; uint8_t v_useContext_1701_; uint8_t v_onlyGivenNames_1702_; uint8_t v_preserveBinderNames_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1714_; 
v_proofs_1694_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1695_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1696_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_descend_1697_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1698_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1699_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1700_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1701_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1702_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1703_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1705_ = v_config_1279_;
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_config_1279_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 0, v_proofs_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 1, v_types_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 2, v_implicits_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 3, v_descend_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 4, v_underBinder_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 5, v_usedOnly_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 6, v_merge_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 7, v_useContext_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 8, v_onlyGivenNames_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, 9, v_preserveBinderNames_1703_);
v___x_1708_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
uint8_t v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1708_, 10, v___x_1709_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1708_);
v___x_1711_ = v___x_1692_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1708_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v_config_1279_);
v_a_1716_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1689_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1689_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1724_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1687_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1687_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_1733_ = lean_string_dec_eq(v___x_1295_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_1735_ = lean_string_dec_eq(v___x_1295_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_1737_ = lean_string_dec_eq(v___x_1295_, v___x_1736_);
lean_dec_ref(v___x_1295_);
if (v___x_1737_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_1739_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1738_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1739_) == 0)
{
uint8_t v___x_1740_; 
lean_dec_ref_known(v___x_1739_, 1);
v___x_1740_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1741_; 
lean_dec_ref(v___x_1296_);
v___x_1741_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1767_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1767_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1767_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
uint8_t v_proofs_1746_; uint8_t v_types_1747_; uint8_t v_descend_1748_; uint8_t v_underBinder_1749_; uint8_t v_usedOnly_1750_; uint8_t v_merge_1751_; uint8_t v_useContext_1752_; uint8_t v_onlyGivenNames_1753_; uint8_t v_preserveBinderNames_1754_; uint8_t v_lift_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1766_; 
v_proofs_1746_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1747_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_descend_1748_ = lean_ctor_get_uint8(v_config_1279_, 3);
v_underBinder_1749_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1750_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1751_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1752_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1753_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1754_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1755_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1757_ = v_config_1279_;
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
else
{
lean_dec(v_config_1279_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 0, v_proofs_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 1, v_types_1747_);
v___x_1760_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
uint8_t v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_unbox(v_a_1742_);
lean_dec(v_a_1742_);
lean_ctor_set_uint8(v___x_1760_, 2, v___x_1761_);
lean_ctor_set_uint8(v___x_1760_, 3, v_descend_1748_);
lean_ctor_set_uint8(v___x_1760_, 4, v_underBinder_1749_);
lean_ctor_set_uint8(v___x_1760_, 5, v_usedOnly_1750_);
lean_ctor_set_uint8(v___x_1760_, 6, v_merge_1751_);
lean_ctor_set_uint8(v___x_1760_, 7, v_useContext_1752_);
lean_ctor_set_uint8(v___x_1760_, 8, v_onlyGivenNames_1753_);
lean_ctor_set_uint8(v___x_1760_, 9, v_preserveBinderNames_1754_);
lean_ctor_set_uint8(v___x_1760_, 10, v_lift_1755_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1760_);
v___x_1763_ = v___x_1744_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1760_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_config_1279_);
v_a_1768_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1741_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1741_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1776_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1739_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1739_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v___x_1295_);
v___x_1784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_1785_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1280_, v___x_1784_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1785_) == 0)
{
uint8_t v___x_1786_; 
lean_dec_ref_known(v___x_1785_, 1);
v___x_1786_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1787_; 
lean_dec_ref(v___x_1296_);
v___x_1787_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1813_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1813_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1813_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
uint8_t v_proofs_1792_; uint8_t v_types_1793_; uint8_t v_implicits_1794_; uint8_t v_underBinder_1795_; uint8_t v_usedOnly_1796_; uint8_t v_merge_1797_; uint8_t v_useContext_1798_; uint8_t v_onlyGivenNames_1799_; uint8_t v_preserveBinderNames_1800_; uint8_t v_lift_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1812_; 
v_proofs_1792_ = lean_ctor_get_uint8(v_config_1279_, 0);
v_types_1793_ = lean_ctor_get_uint8(v_config_1279_, 1);
v_implicits_1794_ = lean_ctor_get_uint8(v_config_1279_, 2);
v_underBinder_1795_ = lean_ctor_get_uint8(v_config_1279_, 4);
v_usedOnly_1796_ = lean_ctor_get_uint8(v_config_1279_, 5);
v_merge_1797_ = lean_ctor_get_uint8(v_config_1279_, 6);
v_useContext_1798_ = lean_ctor_get_uint8(v_config_1279_, 7);
v_onlyGivenNames_1799_ = lean_ctor_get_uint8(v_config_1279_, 8);
v_preserveBinderNames_1800_ = lean_ctor_get_uint8(v_config_1279_, 9);
v_lift_1801_ = lean_ctor_get_uint8(v_config_1279_, 10);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_config_1279_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1803_ = v_config_1279_;
v_isShared_1804_ = v_isSharedCheck_1812_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v_config_1279_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1812_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, 0, v_proofs_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, 1, v_types_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, 2, v_implicits_1794_);
v___x_1806_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
uint8_t v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
lean_ctor_set_uint8(v___x_1806_, 3, v___x_1807_);
lean_ctor_set_uint8(v___x_1806_, 4, v_underBinder_1795_);
lean_ctor_set_uint8(v___x_1806_, 5, v_usedOnly_1796_);
lean_ctor_set_uint8(v___x_1806_, 6, v_merge_1797_);
lean_ctor_set_uint8(v___x_1806_, 7, v_useContext_1798_);
lean_ctor_set_uint8(v___x_1806_, 8, v_onlyGivenNames_1799_);
lean_ctor_set_uint8(v___x_1806_, 9, v_preserveBinderNames_1800_);
lean_ctor_set_uint8(v___x_1806_, 10, v_lift_1801_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1806_);
v___x_1809_ = v___x_1790_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1806_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_config_1279_);
v_a_1814_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1787_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1787_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1822_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1785_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1785_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
uint8_t v___x_1830_; 
lean_dec_ref(v___x_1295_);
lean_dec_ref(v_config_1279_);
v___x_1830_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1296_);
if (v___x_1830_ == 0)
{
lean_dec_ref(v_item_1280_);
v_item_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
lean_object* v_value_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v___x_1296_);
v_value_1831_ = lean_ctor_get(v_item_1280_, 2);
lean_inc(v_value_1831_);
lean_dec_ref(v_item_1280_);
v___x_1832_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_value_1831_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1832_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_1279_);
v_item_1289_ = v_item_1280_;
goto v___jp_1288_;
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v_item_1280_);
lean_dec_ref(v_config_1279_);
v_a_1833_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1293_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1293_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_1291_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1289_, v___x_1290_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1841_, lean_object* v_item_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(v_config_1841_, v_item_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1853_, v___y_1857_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(v_e_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1889_, lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1899_, v_msg_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1909_, lean_object* v_macroStack_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1909_, v_macroStack_1910_, v___y_1915_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1919_, lean_object* v_macroStack_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1919_, v_macroStack_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1928_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1931_ = l_Lean_mkConst(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(lean_object* v_cfg_1934_, lean_object* v_cfgItem_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1);
v___x_1944_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1934_, v_cfgItem_1935_, v___x_1943_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_1945_, lean_object* v_cfgItem_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(v_cfg_1945_, v_cfgItem_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v_cfgItem_1946_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_cfg_1956_, lean_object* v_init_1957_, uint8_t v_logExceptions_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_onErr_1963_; lean_object* v_eval_1964_; 
v_onErr_1963_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v_eval_1964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_1958_ == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1964_, v_init_1957_, v_cfg_1956_, v_onErr_1963_, v_logExceptions_1958_, v_a_1960_, v_a_1961_);
return v___x_1965_;
}
else
{
uint8_t v_recover_1966_; lean_object* v___x_1967_; 
v_recover_1966_ = lean_ctor_get_uint8(v_a_1959_, sizeof(void*)*1);
v___x_1967_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1964_, v_init_1957_, v_cfg_1956_, v_onErr_1963_, v_recover_1966_, v_a_1960_, v_a_1961_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_cfg_1968_, lean_object* v_init_1969_, lean_object* v_logExceptions_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
uint8_t v_logExceptions_boxed_1975_; lean_object* v_res_1976_; 
v_logExceptions_boxed_1975_ = lean_unbox(v_logExceptions_1970_);
v_res_1976_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_1968_, v_init_1969_, v_logExceptions_boxed_1975_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_cfg_1977_, lean_object* v_init_1978_, uint8_t v_logExceptions_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_1977_, v_init_1978_, v_logExceptions_1979_, v_a_1980_, v_a_1986_, v_a_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_cfg_1990_, lean_object* v_init_1991_, lean_object* v_logExceptions_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_logExceptions_boxed_2002_; lean_object* v_res_2003_; 
v_logExceptions_boxed_2002_ = lean_unbox(v_logExceptions_1992_);
v_res_2003_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_cfg_1990_, v_init_1991_, v_logExceptions_boxed_2002_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
return v_res_2003_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0);
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_ref_2040_; lean_object* v___x_2041_; lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_ref_2040_ = lean_ctor_get(v___y_2037_, 2);
v___x_2041_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_inc(v_ref_2040_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_ref_2040_);
lean_ctor_set(v___x_2046_, 1, v_a_2042_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 0, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v_msg_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v_msg_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_2072_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_2071_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v_x_2073_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_2084_, lean_object* v___x_2085_, lean_object* v_a_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2088_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_2097_, v_h_2084_, v___x_2085_, v_a_2086_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v_fst_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2127_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v_fst_2100_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_fst_2100_);
v_snd_2101_ = lean_ctor_get(v_a_2099_, 1);
lean_inc(v_snd_2101_);
lean_dec(v_a_2099_);
v_fst_2102_ = lean_ctor_get(v_fst_2100_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_fst_2100_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_fst_2100_, 1);
lean_dec(v_unused_2128_);
v___x_2104_ = v_fst_2100_;
v_isShared_2105_ = v_isSharedCheck_2127_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_fst_2102_);
lean_dec(v_fst_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2127_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(0);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
lean_ctor_set(v___x_2104_, 1, v___x_2106_);
lean_ctor_set(v___x_2104_, 0, v_snd_2101_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_snd_2101_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2108_, v___y_2088_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2117_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v_fst_2102_);
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_fst_2102_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_fst_2102_);
v_a_2118_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2109_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2109_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2098_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2098_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_a_2086_);
lean_dec(v___x_2085_);
lean_dec(v_h_2084_);
v_a_2137_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2096_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2096_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_2145_, lean_object* v___x_2146_, lean_object* v_a_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_2145_, v___x_2146_, v_a_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_2158_, lean_object* v_a_2159_, lean_object* v_ids_2160_, lean_object* v_h_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; 
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2171_, 0, v_h_2161_);
lean_closure_set(v___f_2171_, 1, v___x_2158_);
lean_closure_set(v___f_2171_, 2, v_a_2159_);
v___x_2172_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2171_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2160_, v_a_2173_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2174_;
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v_ids_2160_);
v_a_2175_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2172_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2172_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_2183_, lean_object* v_a_2184_, lean_object* v_ids_2185_, lean_object* v_h_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_2183_, v_a_2184_, v_ids_2185_, v_h_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_2197_, lean_object* v_a_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2200_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = l_Lean_MVarId_extractLets(v_a_2209_, v___x_2197_, v_a_2198_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v_fst_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2239_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v_fst_2212_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_fst_2212_);
v_snd_2213_ = lean_ctor_get(v_a_2211_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_a_2211_);
v_fst_2214_ = lean_ctor_get(v_fst_2212_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_fst_2212_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v_fst_2212_, 1);
lean_dec(v_unused_2240_);
v___x_2216_ = v_fst_2212_;
v_isShared_2217_ = v_isSharedCheck_2239_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_fst_2214_);
lean_dec(v_fst_2212_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2239_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_box(0);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 1);
lean_ctor_set(v___x_2216_, 1, v___x_2218_);
lean_ctor_set(v___x_2216_, 0, v_snd_2213_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_snd_2213_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2220_, v___y_2200_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2221_, 0);
lean_dec(v_unused_2229_);
v___x_2223_ = v___x_2221_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v___x_2221_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_fst_2214_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_fst_2214_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_fst_2214_);
v_a_2230_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2221_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2221_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2210_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2210_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_a_2198_);
lean_dec(v___x_2197_);
v_a_2249_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2208_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2208_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_2257_, lean_object* v_a_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_2257_, v_a_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_2269_, lean_object* v_ids_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2269_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2270_, v_a_2281_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2282_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_ids_2270_);
v_a_2283_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_2291_, lean_object* v_ids_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_2291_, v_ids_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_2303_, size_t v_i_2304_, lean_object* v_bs_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_lt(v_i_2304_, v_sz_2303_);
if (v___x_2306_ == 0)
{
return v_bs_2305_;
}
else
{
lean_object* v_v_2307_; lean_object* v___x_2308_; lean_object* v_bs_x27_2309_; lean_object* v___x_2310_; size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v_v_2307_ = lean_array_uget(v_bs_2305_, v_i_2304_);
v___x_2308_ = lean_unsigned_to_nat(0u);
v_bs_x27_2309_ = lean_array_uset(v_bs_2305_, v_i_2304_, v___x_2308_);
v___x_2310_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_2307_);
lean_dec(v_v_2307_);
v___x_2311_ = ((size_t)1ULL);
v___x_2312_ = lean_usize_add(v_i_2304_, v___x_2311_);
v___x_2313_ = lean_array_uset(v_bs_x27_2309_, v_i_2304_, v___x_2310_);
v_i_2304_ = v___x_2312_;
v_bs_2305_ = v___x_2313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_2315_, lean_object* v_i_2316_, lean_object* v_bs_2317_){
_start:
{
size_t v_sz_boxed_2318_; size_t v_i_boxed_2319_; lean_object* v_res_2320_; 
v_sz_boxed_2318_ = lean_unbox_usize(v_sz_2315_);
lean_dec(v_sz_2315_);
v_i_boxed_2319_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_2318_, v_i_boxed_2319_, v_bs_2317_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_2341_);
v___x_2352_ = l_Lean_Syntax_isOfKind(v_x_2341_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_x_2341_);
v___x_2353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2355_);
v___x_2357_ = l_Lean_Syntax_isOfKind(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_dec(v___x_2355_);
lean_dec(v_x_2341_);
v___x_2358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2358_;
}
else
{
lean_object* v___f_2359_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_loc_x3f_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___f_2359_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_2375_ = lean_unsigned_to_nat(2u);
v___x_2376_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2375_);
v___x_2416_ = lean_unsigned_to_nat(3u);
v___x_2417_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2416_);
lean_dec(v_x_2341_);
v___x_2418_ = l_Lean_Syntax_isNone(v___x_2417_);
if (v___x_2418_ == 0)
{
uint8_t v___x_2419_; 
lean_inc(v___x_2417_);
v___x_2419_ = l_Lean_Syntax_matchesNull(v___x_2417_, v___x_2354_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec(v___x_2417_);
lean_dec(v___x_2376_);
lean_dec(v___x_2355_);
v___x_2420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v_loc_x3f_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2422_ = l_Lean_Syntax_getArg(v___x_2417_, v___x_2421_);
lean_dec(v___x_2417_);
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2422_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_dec(v_loc_x3f_2422_);
lean_dec(v___x_2376_);
lean_dec(v___x_2355_);
v___x_2425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_loc_x3f_2422_);
v_loc_x3f_2378_ = v___x_2426_;
v___y_2379_ = v_a_2342_;
v___y_2380_ = v_a_2343_;
v___y_2381_ = v_a_2344_;
v___y_2382_ = v_a_2345_;
v___y_2383_ = v_a_2346_;
v___y_2384_ = v_a_2347_;
v___y_2385_ = v_a_2348_;
v___y_2386_ = v_a_2349_;
goto v___jp_2377_;
}
}
}
else
{
lean_object* v___x_2427_; 
lean_dec(v___x_2417_);
v___x_2427_ = lean_box(0);
v_loc_x3f_2378_ = v___x_2427_;
v___y_2379_ = v_a_2342_;
v___y_2380_ = v_a_2343_;
v___y_2381_ = v_a_2344_;
v___y_2382_ = v_a_2345_;
v___y_2383_ = v_a_2346_;
v___y_2384_ = v_a_2347_;
v___y_2385_ = v_a_2348_;
v___y_2386_ = v_a_2349_;
goto v___jp_2377_;
}
v___jp_2360_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = l_Lean_mkOptionalNode(v___y_2371_);
v___x_2373_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2372_);
lean_dec(v___x_2372_);
v___x_2374_ = l_Lean_Elab_Tactic_withLocation(v___x_2373_, v___y_2363_, v___y_2364_, v___f_2359_, v___y_2362_, v___y_2361_, v___y_2368_, v___y_2367_, v___y_2366_, v___y_2365_, v___y_2369_, v___y_2370_);
lean_dec(v___x_2373_);
return v___x_2374_;
}
v___jp_2377_:
{
lean_object* v_ids_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_ids_2387_ = l_Lean_Syntax_getArgs(v___x_2376_);
lean_dec(v___x_2376_);
v___x_2388_ = 0;
v___x_2389_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2389_, 0, v___x_2388_);
lean_ctor_set_uint8(v___x_2389_, 1, v___x_2357_);
lean_ctor_set_uint8(v___x_2389_, 2, v___x_2388_);
lean_ctor_set_uint8(v___x_2389_, 3, v___x_2357_);
lean_ctor_set_uint8(v___x_2389_, 4, v___x_2357_);
lean_ctor_set_uint8(v___x_2389_, 5, v___x_2388_);
lean_ctor_set_uint8(v___x_2389_, 6, v___x_2357_);
lean_ctor_set_uint8(v___x_2389_, 7, v___x_2357_);
lean_ctor_set_uint8(v___x_2389_, 8, v___x_2388_);
lean_ctor_set_uint8(v___x_2389_, 9, v___x_2388_);
lean_ctor_set_uint8(v___x_2389_, 10, v___x_2388_);
v___x_2390_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_2355_, v___x_2389_, v___x_2357_, v___y_2379_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; size_t v_sz_2392_; size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc_n(v_a_2391_, 2);
lean_dec_ref_known(v___x_2390_, 1);
v_sz_2392_ = lean_array_size(v_ids_2387_);
v___x_2393_ = ((size_t)0ULL);
lean_inc_ref_n(v_ids_2387_, 2);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_2392_, v___x_2393_, v_ids_2387_);
v___x_2395_ = lean_array_to_list(v___x_2394_);
lean_inc(v___x_2395_);
v___f_2396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_2396_, 0, v___x_2395_);
lean_closure_set(v___f_2396_, 1, v_a_2391_);
lean_closure_set(v___f_2396_, 2, v_ids_2387_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2397_, 0, v___x_2395_);
lean_closure_set(v___f_2397_, 1, v_a_2391_);
v___f_2398_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_2398_, 0, v___f_2397_);
lean_closure_set(v___f_2398_, 1, v_ids_2387_);
if (lean_obj_tag(v_loc_x3f_2378_) == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_box(0);
v___y_2361_ = v___y_2380_;
v___y_2362_ = v___y_2379_;
v___y_2363_ = v___f_2396_;
v___y_2364_ = v___f_2398_;
v___y_2365_ = v___y_2384_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___y_2382_;
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___x_2399_;
goto v___jp_2360_;
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_val_2400_ = lean_ctor_get(v_loc_x3f_2378_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_loc_x3f_2378_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v_loc_x3f_2378_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v_loc_x3f_2378_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_val_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
v___y_2361_ = v___y_2380_;
v___y_2362_ = v___y_2379_;
v___y_2363_ = v___f_2396_;
v___y_2364_ = v___f_2398_;
v___y_2365_ = v___y_2384_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___y_2382_;
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___x_2405_;
goto v___jp_2360_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v_ids_2387_);
lean_dec(v_loc_x3f_2378_);
v_a_2408_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2390_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2390_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_2439_, lean_object* v_msg_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v_msg_2440_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_2451_, v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2470_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_2472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_2473_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_2474_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2470_, v___x_2471_, v___x_2472_, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object* v___x_2477_, lean_object* v_ctor_2478_, lean_object* v_args_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_2506_ = lean_string_dec_eq(v_ctor_2478_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2508_ = lean_array_get_size(v_args_2479_);
v___x_2509_ = lean_unsigned_to_nat(1u);
v___x_2510_ = lean_nat_dec_eq(v___x_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_2512_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_2511_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
goto v___jp_2485_;
}
}
v___jp_2485_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_array_get_borrowed(v___x_2477_, v_args_2479_, v___x_2486_);
lean_inc(v___x_2487_);
v___x_2488_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v___x_2487_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v_a_2497_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2488_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2488_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object* v___x_2521_, lean_object* v_ctor_2522_, lean_object* v_args_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(v___x_2521_, v_ctor_2522_, v_args_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_args_2523_);
lean_dec_ref(v_ctor_2522_);
lean_dec_ref(v___x_2521_);
return v_res_2529_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___f_2531_; 
v___x_2530_ = l_Lean_instInhabitedExpr;
v___f_2531_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2531_, 0, v___x_2530_);
return v___f_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___f_2543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0);
v___x_2544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2545_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2544_, v___f_2543_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
return v_res_2552_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2556_ = l_Lean_Expr_const___override(v___x_2555_, v___x_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0));
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2559_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig(void){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2564_ = l_Lean_MessageData_ofExpr(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0);
v___x_2566_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___x_2565_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_2569_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_ty_x3f_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_toCold_2585_; lean_object* v_currRecDepth_2586_; lean_object* v_ref_2587_; uint16_t v_optionFlags_2588_; uint8_t v_suppressElabErrors_2589_; uint8_t v_isRecordingDeps_2590_; uint8_t v___x_2591_; lean_object* v_ref_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_ty_x3f_2579_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2580_ = 1;
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_box(v___x_2580_);
v___x_2583_ = lean_box(v___x_2580_);
lean_inc(v_stx_2571_);
v___x_2584_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2584_, 0, v_stx_2571_);
lean_closure_set(v___x_2584_, 1, v_ty_x3f_2579_);
lean_closure_set(v___x_2584_, 2, v___x_2582_);
lean_closure_set(v___x_2584_, 3, v___x_2583_);
lean_closure_set(v___x_2584_, 4, v___x_2581_);
v_toCold_2585_ = lean_ctor_get(v_a_2576_, 0);
v_currRecDepth_2586_ = lean_ctor_get(v_a_2576_, 1);
v_ref_2587_ = lean_ctor_get(v_a_2576_, 2);
v_optionFlags_2588_ = lean_ctor_get_uint16(v_a_2576_, sizeof(void*)*3);
v_suppressElabErrors_2589_ = lean_ctor_get_uint8(v_a_2576_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2590_ = lean_ctor_get_uint8(v_a_2576_, sizeof(void*)*3 + 3);
v___x_2591_ = 1;
v_ref_2592_ = l_Lean_replaceRef(v_stx_2571_, v_ref_2587_);
lean_dec(v_stx_2571_);
lean_inc(v_currRecDepth_2586_);
lean_inc_ref(v_toCold_2585_);
v___x_2593_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2593_, 0, v_toCold_2585_);
lean_ctor_set(v___x_2593_, 1, v_currRecDepth_2586_);
lean_ctor_set(v___x_2593_, 2, v_ref_2592_);
lean_ctor_set_uint16(v___x_2593_, sizeof(void*)*3, v_optionFlags_2588_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3 + 2, v_suppressElabErrors_2589_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3 + 3, v_isRecordingDeps_2590_);
v___x_2594_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2584_, v___x_2591_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v___x_2593_, v_a_2577_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; lean_object* v_a_2597_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; uint8_t v___x_2681_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_2595_, v_a_2575_);
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2596_);
v___x_2681_ = l_Lean_Expr_hasSorry(v_a_2597_);
if (v___x_2681_ == 0)
{
v___y_2626_ = v_a_2572_;
v___y_2627_ = v_a_2573_;
v___y_2628_ = v_a_2574_;
v___y_2629_ = v_a_2575_;
v___y_2630_ = v___x_2593_;
v___y_2631_ = v_a_2577_;
goto v___jp_2625_;
}
else
{
uint8_t v___x_2682_; 
v___x_2682_ = l_Lean_Expr_hasSyntheticSorry(v_a_2597_);
if (v___x_2682_ == 0)
{
v___y_2663_ = v_a_2572_;
v___y_2664_ = v_a_2573_;
v___y_2665_ = v_a_2574_;
v___y_2666_ = v_a_2575_;
v___y_2667_ = v___x_2593_;
v___y_2668_ = v_a_2577_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_a_2597_);
lean_dec_ref_known(v___x_2593_, 3);
v___x_2683_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
v___jp_2598_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_2597_);
v___x_2606_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2597_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_dec_ref(v___y_2603_);
lean_dec(v_a_2597_);
return v___x_2606_;
}
else
{
lean_object* v_a_2607_; uint8_t v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
v___x_2608_ = l_Lean_Exception_isInterrupt(v_a_2607_);
if (v___x_2608_ == 0)
{
uint8_t v___x_2609_; 
lean_inc(v_a_2607_);
v___x_2609_ = l_Lean_Exception_isRuntime(v_a_2607_);
if (v___x_2609_ == 0)
{
if (lean_obj_tag(v_a_2607_) == 0)
{
lean_dec_ref_known(v_a_2607_, 2);
lean_dec_ref(v___y_2603_);
lean_dec(v_a_2597_);
return v___x_2606_;
}
else
{
lean_object* v_id_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2623_; 
v_id_2610_ = lean_ctor_get(v_a_2607_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2607_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v_a_2607_, 1);
lean_dec(v_unused_2624_);
v___x_2612_ = v_a_2607_;
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_id_2610_);
lean_dec(v_a_2607_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v___x_2614_; 
v___x_2614_ = l_Lean_instBEqInternalExceptionId_beq(v___x_2605_, v_id_2610_);
lean_dec(v_id_2610_);
if (v___x_2614_ == 0)
{
lean_del_object(v___x_2612_);
lean_dec_ref(v___y_2603_);
lean_dec(v_a_2597_);
return v___x_2606_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2606_, 1);
v___x_2615_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_2616_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_2617_ = l_Lean_indentExpr(v_a_2597_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 7);
lean_ctor_set(v___x_2612_, 1, v___x_2617_);
lean_ctor_set(v___x_2612_, 0, v___x_2616_);
v___x_2619_ = v___x_2612_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2615_);
v___x_2621_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2620_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec_ref(v___y_2603_);
return v___x_2621_;
}
}
}
}
}
else
{
lean_dec(v_a_2607_);
lean_dec_ref(v___y_2603_);
lean_dec(v_a_2597_);
return v___x_2606_;
}
}
else
{
lean_dec(v_a_2607_);
lean_dec_ref(v___y_2603_);
lean_dec(v_a_2597_);
return v___x_2606_;
}
}
}
v___jp_2625_:
{
lean_object* v___x_2632_; 
lean_inc(v_a_2597_);
v___x_2632_ = l_Lean_Meta_getMVars(v_a_2597_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2633_, v___x_2581_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v_a_2633_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; uint8_t v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = lean_unbox(v_a_2635_);
lean_dec(v_a_2635_);
if (v___x_2636_ == 0)
{
v___y_2599_ = v___y_2626_;
v___y_2600_ = v___y_2627_;
v___y_2601_ = v___y_2628_;
v___y_2602_ = v___y_2629_;
v___y_2603_ = v___y_2630_;
v___y_2604_ = v___y_2631_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2637_; lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___y_2630_);
lean_dec(v_a_2597_);
v___x_2637_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___y_2630_);
lean_dec(v_a_2597_);
v_a_2646_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2634_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2634_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v___y_2630_);
lean_dec(v_a_2597_);
v_a_2654_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2632_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2632_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
v___jp_2662_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v___x_2669_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_2670_ = l_Lean_indentExpr(v_a_2597_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2671_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec_ref(v___y_2667_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref_known(v___x_2593_, 3);
v_a_2692_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2594_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2594_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_stx_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(lean_object* v_config_2711_, lean_object* v_item_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_item_2721_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2725_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2712_, v___x_2724_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2725_) == 0)
{
uint8_t v___x_2726_; 
lean_dec_ref_known(v___x_2725_, 1);
v___x_2726_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_2712_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2727_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_2712_);
lean_inc_ref(v_item_2712_);
v___x_2728_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_2712_);
v___x_2729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_2730_ = lean_string_dec_lt(v___x_2727_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_2732_ = lean_string_dec_lt(v___x_2727_, v___x_2731_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_string_dec_eq(v___x_2727_, v___x_2731_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_2735_ = lean_string_dec_eq(v___x_2727_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_2737_ = lean_string_dec_eq(v___x_2727_, v___x_2736_);
lean_dec_ref(v___x_2727_);
if (v___x_2737_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_2739_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2738_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2739_) == 0)
{
uint8_t v___x_2740_; 
lean_dec_ref_known(v___x_2739_, 1);
v___x_2740_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2740_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2741_; 
lean_dec_ref(v___x_2728_);
v___x_2741_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2767_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2767_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2767_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
uint8_t v_proofs_2746_; uint8_t v_types_2747_; uint8_t v_implicits_2748_; uint8_t v_descend_2749_; uint8_t v_underBinder_2750_; uint8_t v_merge_2751_; uint8_t v_useContext_2752_; uint8_t v_onlyGivenNames_2753_; uint8_t v_preserveBinderNames_2754_; uint8_t v_lift_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2766_; 
v_proofs_2746_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_2747_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_2748_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2749_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_2750_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_merge_2751_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_2752_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_2753_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_2754_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_2755_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2757_ = v_config_2711_;
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
else
{
lean_dec(v_config_2711_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, 0, v_proofs_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, 1, v_types_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, 2, v_implicits_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, 3, v_descend_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, 4, v_underBinder_2750_);
v___x_2760_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
uint8_t v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = lean_unbox(v_a_2742_);
lean_dec(v_a_2742_);
lean_ctor_set_uint8(v___x_2760_, 5, v___x_2761_);
lean_ctor_set_uint8(v___x_2760_, 6, v_merge_2751_);
lean_ctor_set_uint8(v___x_2760_, 7, v_useContext_2752_);
lean_ctor_set_uint8(v___x_2760_, 8, v_onlyGivenNames_2753_);
lean_ctor_set_uint8(v___x_2760_, 9, v_preserveBinderNames_2754_);
lean_ctor_set_uint8(v___x_2760_, 10, v_lift_2755_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2760_);
v___x_2763_ = v___x_2744_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2760_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_config_2711_);
v_a_2768_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2741_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2741_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_2776_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2739_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2739_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec_ref(v___x_2727_);
v___x_2784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_2785_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2784_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2785_) == 0)
{
uint8_t v___x_2786_; 
lean_dec_ref_known(v___x_2785_, 1);
v___x_2786_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2786_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref(v___x_2728_);
v___x_2787_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2813_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2813_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2813_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
uint8_t v_proofs_2792_; uint8_t v_types_2793_; uint8_t v_implicits_2794_; uint8_t v_descend_2795_; uint8_t v_underBinder_2796_; uint8_t v_usedOnly_2797_; uint8_t v_merge_2798_; uint8_t v_onlyGivenNames_2799_; uint8_t v_preserveBinderNames_2800_; uint8_t v_lift_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2812_; 
v_proofs_2792_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_2793_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_2794_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2795_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_2796_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_2797_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_2798_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_onlyGivenNames_2799_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_2800_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_2801_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2803_ = v_config_2711_;
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
else
{
lean_dec(v_config_2711_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 0, v_proofs_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 1, v_types_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 2, v_implicits_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 3, v_descend_2795_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 4, v_underBinder_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 5, v_usedOnly_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, 6, v_merge_2798_);
v___x_2806_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
uint8_t v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
lean_ctor_set_uint8(v___x_2806_, 7, v___x_2807_);
lean_ctor_set_uint8(v___x_2806_, 8, v_onlyGivenNames_2799_);
lean_ctor_set_uint8(v___x_2806_, 9, v_preserveBinderNames_2800_);
lean_ctor_set_uint8(v___x_2806_, 10, v_lift_2801_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2806_);
v___x_2809_ = v___x_2790_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2806_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v_config_2711_);
v_a_2814_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2787_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2787_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_2822_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2785_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2785_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v___x_2727_);
v___x_2830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_2831_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2830_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2831_) == 0)
{
uint8_t v___x_2832_; 
lean_dec_ref_known(v___x_2831_, 1);
v___x_2832_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2832_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2833_; 
lean_dec_ref(v___x_2728_);
v___x_2833_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2859_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2859_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2859_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v_proofs_2838_; uint8_t v_types_2839_; uint8_t v_implicits_2840_; uint8_t v_descend_2841_; uint8_t v_usedOnly_2842_; uint8_t v_merge_2843_; uint8_t v_useContext_2844_; uint8_t v_onlyGivenNames_2845_; uint8_t v_preserveBinderNames_2846_; uint8_t v_lift_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2858_; 
v_proofs_2838_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_2839_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_2840_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2841_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_usedOnly_2842_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_2843_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_2844_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_2845_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_2846_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_2847_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2849_ = v_config_2711_;
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
else
{
lean_dec(v_config_2711_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, 0, v_proofs_2838_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, 1, v_types_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, 2, v_implicits_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, 3, v_descend_2841_);
v___x_2852_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
uint8_t v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
lean_ctor_set_uint8(v___x_2852_, 4, v___x_2853_);
lean_ctor_set_uint8(v___x_2852_, 5, v_usedOnly_2842_);
lean_ctor_set_uint8(v___x_2852_, 6, v_merge_2843_);
lean_ctor_set_uint8(v___x_2852_, 7, v_useContext_2844_);
lean_ctor_set_uint8(v___x_2852_, 8, v_onlyGivenNames_2845_);
lean_ctor_set_uint8(v___x_2852_, 9, v_preserveBinderNames_2846_);
lean_ctor_set_uint8(v___x_2852_, 10, v_lift_2847_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2852_);
v___x_2855_ = v___x_2836_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2852_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_config_2711_);
v_a_2860_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2833_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2833_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_2868_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2831_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2831_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
else
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_string_dec_eq(v___x_2727_, v___x_2729_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_2878_ = lean_string_dec_eq(v___x_2727_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_2880_ = lean_string_dec_eq(v___x_2727_, v___x_2879_);
lean_dec_ref(v___x_2727_);
if (v___x_2880_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_2882_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2881_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2882_) == 0)
{
uint8_t v___x_2883_; 
lean_dec_ref_known(v___x_2882_, 1);
v___x_2883_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2883_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2884_; 
lean_dec_ref(v___x_2728_);
v___x_2884_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2910_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2910_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2910_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
uint8_t v_proofs_2889_; uint8_t v_implicits_2890_; uint8_t v_descend_2891_; uint8_t v_underBinder_2892_; uint8_t v_usedOnly_2893_; uint8_t v_merge_2894_; uint8_t v_useContext_2895_; uint8_t v_onlyGivenNames_2896_; uint8_t v_preserveBinderNames_2897_; uint8_t v_lift_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2909_; 
v_proofs_2889_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_implicits_2890_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2891_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_2892_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_2893_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_2894_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_2895_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_2896_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_2897_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_2898_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2900_ = v_config_2711_;
v_isShared_2901_ = v_isSharedCheck_2909_;
goto v_resetjp_2899_;
}
else
{
lean_dec(v_config_2711_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2909_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 0, v_proofs_2889_);
v___x_2903_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
uint8_t v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_unbox(v_a_2885_);
lean_dec(v_a_2885_);
lean_ctor_set_uint8(v___x_2903_, 1, v___x_2904_);
lean_ctor_set_uint8(v___x_2903_, 2, v_implicits_2890_);
lean_ctor_set_uint8(v___x_2903_, 3, v_descend_2891_);
lean_ctor_set_uint8(v___x_2903_, 4, v_underBinder_2892_);
lean_ctor_set_uint8(v___x_2903_, 5, v_usedOnly_2893_);
lean_ctor_set_uint8(v___x_2903_, 6, v_merge_2894_);
lean_ctor_set_uint8(v___x_2903_, 7, v_useContext_2895_);
lean_ctor_set_uint8(v___x_2903_, 8, v_onlyGivenNames_2896_);
lean_ctor_set_uint8(v___x_2903_, 9, v_preserveBinderNames_2897_);
lean_ctor_set_uint8(v___x_2903_, 10, v_lift_2898_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2903_);
v___x_2906_ = v___x_2887_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2903_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_config_2711_);
v_a_2911_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2884_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2884_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_2919_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2882_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2882_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec_ref(v___x_2727_);
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_2928_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2927_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2928_) == 0)
{
uint8_t v___x_2929_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2930_; 
lean_dec_ref(v___x_2728_);
v___x_2930_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2956_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
uint8_t v_types_2935_; uint8_t v_implicits_2936_; uint8_t v_descend_2937_; uint8_t v_underBinder_2938_; uint8_t v_usedOnly_2939_; uint8_t v_merge_2940_; uint8_t v_useContext_2941_; uint8_t v_onlyGivenNames_2942_; uint8_t v_preserveBinderNames_2943_; uint8_t v_lift_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2955_; 
v_types_2935_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_2936_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2937_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_2938_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_2939_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_2940_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_2941_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_2942_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_2943_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_2944_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2946_ = v_config_2711_;
v_isShared_2947_ = v_isSharedCheck_2955_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_config_2711_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2955_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 0, 11);
v___x_2949_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
uint8_t v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_unbox(v_a_2931_);
lean_dec(v_a_2931_);
lean_ctor_set_uint8(v___x_2949_, 0, v___x_2950_);
lean_ctor_set_uint8(v___x_2949_, 1, v_types_2935_);
lean_ctor_set_uint8(v___x_2949_, 2, v_implicits_2936_);
lean_ctor_set_uint8(v___x_2949_, 3, v_descend_2937_);
lean_ctor_set_uint8(v___x_2949_, 4, v_underBinder_2938_);
lean_ctor_set_uint8(v___x_2949_, 5, v_usedOnly_2939_);
lean_ctor_set_uint8(v___x_2949_, 6, v_merge_2940_);
lean_ctor_set_uint8(v___x_2949_, 7, v_useContext_2941_);
lean_ctor_set_uint8(v___x_2949_, 8, v_onlyGivenNames_2942_);
lean_ctor_set_uint8(v___x_2949_, 9, v_preserveBinderNames_2943_);
lean_ctor_set_uint8(v___x_2949_, 10, v_lift_2944_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2949_);
v___x_2952_ = v___x_2933_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2949_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v_config_2711_);
v_a_2957_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2930_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2930_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_2965_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2928_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2928_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v___x_2727_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_2974_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_2973_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2974_) == 0)
{
uint8_t v___x_2975_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2976_; 
lean_dec_ref(v___x_2728_);
v___x_2976_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3002_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2979_ = v___x_2976_;
v_isShared_2980_ = v_isSharedCheck_3002_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3002_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
uint8_t v_proofs_2981_; uint8_t v_types_2982_; uint8_t v_implicits_2983_; uint8_t v_descend_2984_; uint8_t v_underBinder_2985_; uint8_t v_usedOnly_2986_; uint8_t v_merge_2987_; uint8_t v_useContext_2988_; uint8_t v_onlyGivenNames_2989_; uint8_t v_lift_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3001_; 
v_proofs_2981_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_2982_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_2983_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_2984_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_2985_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_2986_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_2987_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_2988_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_2989_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_lift_2990_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2992_ = v_config_2711_;
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v_config_2711_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 0, v_proofs_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 1, v_types_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 2, v_implicits_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 3, v_descend_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 4, v_underBinder_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 5, v_usedOnly_2986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 6, v_merge_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 7, v_useContext_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, 8, v_onlyGivenNames_2989_);
v___x_2995_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
uint8_t v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = lean_unbox(v_a_2977_);
lean_dec(v_a_2977_);
lean_ctor_set_uint8(v___x_2995_, 9, v___x_2996_);
lean_ctor_set_uint8(v___x_2995_, 10, v_lift_2990_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2995_);
v___x_2998_ = v___x_2979_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2995_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_config_2711_);
v_a_3003_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2976_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2976_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3011_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2974_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2974_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
else
{
lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_3020_ = lean_string_dec_lt(v___x_2727_, v___x_3019_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_string_dec_eq(v___x_2727_, v___x_3019_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_3023_ = lean_string_dec_eq(v___x_2727_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_3025_ = lean_string_dec_eq(v___x_2727_, v___x_3024_);
lean_dec_ref(v___x_2727_);
if (v___x_3025_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_3027_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_3026_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3027_) == 0)
{
uint8_t v___x_3028_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3028_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3029_; 
lean_dec_ref(v___x_2728_);
v___x_3029_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3055_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3055_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3055_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
uint8_t v_proofs_3034_; uint8_t v_types_3035_; uint8_t v_implicits_3036_; uint8_t v_descend_3037_; uint8_t v_underBinder_3038_; uint8_t v_usedOnly_3039_; uint8_t v_merge_3040_; uint8_t v_useContext_3041_; uint8_t v_preserveBinderNames_3042_; uint8_t v_lift_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3054_; 
v_proofs_3034_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_3035_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_3036_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_3037_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_3038_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_3039_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_3040_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_3041_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_preserveBinderNames_3042_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_3043_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3045_ = v_config_2711_;
v_isShared_3046_ = v_isSharedCheck_3054_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v_config_2711_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3054_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 0, v_proofs_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 1, v_types_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 2, v_implicits_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 3, v_descend_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 4, v_underBinder_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 5, v_usedOnly_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 6, v_merge_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, 7, v_useContext_3041_);
v___x_3048_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
uint8_t v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_unbox(v_a_3030_);
lean_dec(v_a_3030_);
lean_ctor_set_uint8(v___x_3048_, 8, v___x_3049_);
lean_ctor_set_uint8(v___x_3048_, 9, v_preserveBinderNames_3042_);
lean_ctor_set_uint8(v___x_3048_, 10, v_lift_3043_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3048_);
v___x_3051_ = v___x_3032_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3048_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_config_2711_);
v_a_3056_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3029_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3029_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3064_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3027_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3027_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v___x_2727_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_3073_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_3072_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3073_) == 0)
{
uint8_t v___x_3074_; 
lean_dec_ref_known(v___x_3073_, 1);
v___x_3074_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3074_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3075_; 
lean_dec_ref(v___x_2728_);
v___x_3075_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3101_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3101_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3101_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
uint8_t v_proofs_3080_; uint8_t v_types_3081_; uint8_t v_implicits_3082_; uint8_t v_descend_3083_; uint8_t v_underBinder_3084_; uint8_t v_usedOnly_3085_; uint8_t v_useContext_3086_; uint8_t v_onlyGivenNames_3087_; uint8_t v_preserveBinderNames_3088_; uint8_t v_lift_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3100_; 
v_proofs_3080_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_3081_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_3082_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_3083_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_3084_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_3085_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_useContext_3086_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_3087_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_3088_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_3089_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3091_ = v_config_2711_;
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v_config_2711_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 0, v_proofs_3080_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 1, v_types_3081_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 2, v_implicits_3082_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 3, v_descend_3083_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 4, v_underBinder_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, 5, v_usedOnly_3085_);
v___x_3094_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
uint8_t v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_unbox(v_a_3076_);
lean_dec(v_a_3076_);
lean_ctor_set_uint8(v___x_3094_, 6, v___x_3095_);
lean_ctor_set_uint8(v___x_3094_, 7, v_useContext_3086_);
lean_ctor_set_uint8(v___x_3094_, 8, v_onlyGivenNames_3087_);
lean_ctor_set_uint8(v___x_3094_, 9, v_preserveBinderNames_3088_);
lean_ctor_set_uint8(v___x_3094_, 10, v_lift_3089_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3094_);
v___x_3097_ = v___x_3078_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3094_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v_config_2711_);
v_a_3102_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3075_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3075_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3110_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3073_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3073_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref(v___x_2727_);
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_3119_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_3118_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3119_) == 0)
{
uint8_t v___x_3120_; 
lean_dec_ref_known(v___x_3119_, 1);
v___x_3120_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3120_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3121_; 
lean_dec_ref(v___x_2728_);
v___x_3121_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3147_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3147_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3147_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint8_t v_proofs_3126_; uint8_t v_types_3127_; uint8_t v_implicits_3128_; uint8_t v_descend_3129_; uint8_t v_underBinder_3130_; uint8_t v_usedOnly_3131_; uint8_t v_merge_3132_; uint8_t v_useContext_3133_; uint8_t v_onlyGivenNames_3134_; uint8_t v_preserveBinderNames_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3146_; 
v_proofs_3126_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_3127_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_3128_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_descend_3129_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_3130_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_3131_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_3132_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_3133_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_3134_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_3135_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3137_ = v_config_2711_;
v_isShared_3138_ = v_isSharedCheck_3146_;
goto v_resetjp_3136_;
}
else
{
lean_dec(v_config_2711_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3146_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 0, v_proofs_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 1, v_types_3127_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 2, v_implicits_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 3, v_descend_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 4, v_underBinder_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 5, v_usedOnly_3131_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 6, v_merge_3132_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 7, v_useContext_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 8, v_onlyGivenNames_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, 9, v_preserveBinderNames_3135_);
v___x_3140_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
uint8_t v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_unbox(v_a_3122_);
lean_dec(v_a_3122_);
lean_ctor_set_uint8(v___x_3140_, 10, v___x_3141_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3140_);
v___x_3143_ = v___x_3124_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3140_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v_config_2711_);
v_a_3148_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3121_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3121_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3156_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3119_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3119_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
else
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_3165_ = lean_string_dec_eq(v___x_2727_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_3167_ = lean_string_dec_eq(v___x_2727_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_3169_ = lean_string_dec_eq(v___x_2727_, v___x_3168_);
lean_dec_ref(v___x_2727_);
if (v___x_3169_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_3171_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_3170_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3171_) == 0)
{
uint8_t v___x_3172_; 
lean_dec_ref_known(v___x_3171_, 1);
v___x_3172_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3173_; 
lean_dec_ref(v___x_2728_);
v___x_3173_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3199_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3199_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3199_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
uint8_t v_proofs_3178_; uint8_t v_types_3179_; uint8_t v_descend_3180_; uint8_t v_underBinder_3181_; uint8_t v_usedOnly_3182_; uint8_t v_merge_3183_; uint8_t v_useContext_3184_; uint8_t v_onlyGivenNames_3185_; uint8_t v_preserveBinderNames_3186_; uint8_t v_lift_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3198_; 
v_proofs_3178_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_3179_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_descend_3180_ = lean_ctor_get_uint8(v_config_2711_, 3);
v_underBinder_3181_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_3182_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_3183_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_3184_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_3185_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_3186_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_3187_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3189_ = v_config_2711_;
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
else
{
lean_dec(v_config_2711_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 0, v_proofs_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 1, v_types_3179_);
v___x_3192_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
uint8_t v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_unbox(v_a_3174_);
lean_dec(v_a_3174_);
lean_ctor_set_uint8(v___x_3192_, 2, v___x_3193_);
lean_ctor_set_uint8(v___x_3192_, 3, v_descend_3180_);
lean_ctor_set_uint8(v___x_3192_, 4, v_underBinder_3181_);
lean_ctor_set_uint8(v___x_3192_, 5, v_usedOnly_3182_);
lean_ctor_set_uint8(v___x_3192_, 6, v_merge_3183_);
lean_ctor_set_uint8(v___x_3192_, 7, v_useContext_3184_);
lean_ctor_set_uint8(v___x_3192_, 8, v_onlyGivenNames_3185_);
lean_ctor_set_uint8(v___x_3192_, 9, v_preserveBinderNames_3186_);
lean_ctor_set_uint8(v___x_3192_, 10, v_lift_3187_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3192_);
v___x_3195_ = v___x_3176_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3192_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_config_2711_);
v_a_3200_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3173_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3173_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3208_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3171_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3171_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec_ref(v___x_2727_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_3217_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2712_, v___x_3216_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3217_) == 0)
{
uint8_t v___x_3218_; 
lean_dec_ref_known(v___x_3217_, 1);
v___x_3218_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3218_ == 0)
{
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_3219_; 
lean_dec_ref(v___x_2728_);
v___x_3219_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3245_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3245_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3245_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
uint8_t v_proofs_3224_; uint8_t v_types_3225_; uint8_t v_implicits_3226_; uint8_t v_underBinder_3227_; uint8_t v_usedOnly_3228_; uint8_t v_merge_3229_; uint8_t v_useContext_3230_; uint8_t v_onlyGivenNames_3231_; uint8_t v_preserveBinderNames_3232_; uint8_t v_lift_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3244_; 
v_proofs_3224_ = lean_ctor_get_uint8(v_config_2711_, 0);
v_types_3225_ = lean_ctor_get_uint8(v_config_2711_, 1);
v_implicits_3226_ = lean_ctor_get_uint8(v_config_2711_, 2);
v_underBinder_3227_ = lean_ctor_get_uint8(v_config_2711_, 4);
v_usedOnly_3228_ = lean_ctor_get_uint8(v_config_2711_, 5);
v_merge_3229_ = lean_ctor_get_uint8(v_config_2711_, 6);
v_useContext_3230_ = lean_ctor_get_uint8(v_config_2711_, 7);
v_onlyGivenNames_3231_ = lean_ctor_get_uint8(v_config_2711_, 8);
v_preserveBinderNames_3232_ = lean_ctor_get_uint8(v_config_2711_, 9);
v_lift_3233_ = lean_ctor_get_uint8(v_config_2711_, 10);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_config_2711_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3235_ = v_config_2711_;
v_isShared_3236_ = v_isSharedCheck_3244_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v_config_2711_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3244_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, 0, v_proofs_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, 1, v_types_3225_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, 2, v_implicits_3226_);
v___x_3238_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
uint8_t v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
lean_ctor_set_uint8(v___x_3238_, 3, v___x_3239_);
lean_ctor_set_uint8(v___x_3238_, 4, v_underBinder_3227_);
lean_ctor_set_uint8(v___x_3238_, 5, v_usedOnly_3228_);
lean_ctor_set_uint8(v___x_3238_, 6, v_merge_3229_);
lean_ctor_set_uint8(v___x_3238_, 7, v_useContext_3230_);
lean_ctor_set_uint8(v___x_3238_, 8, v_onlyGivenNames_3231_);
lean_ctor_set_uint8(v___x_3238_, 9, v_preserveBinderNames_3232_);
lean_ctor_set_uint8(v___x_3238_, 10, v_lift_3233_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3238_);
v___x_3241_ = v___x_3222_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3238_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec_ref(v_config_2711_);
v_a_3246_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3219_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3219_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3254_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3217_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3217_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
else
{
uint8_t v___x_3262_; 
lean_dec_ref(v___x_2727_);
lean_dec_ref(v_config_2711_);
v___x_3262_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2728_);
if (v___x_3262_ == 0)
{
lean_dec_ref(v_item_2712_);
v_item_2721_ = v___x_2728_;
goto v___jp_2720_;
}
else
{
lean_object* v_value_3263_; lean_object* v___x_3264_; 
lean_dec_ref(v___x_2728_);
v_value_3263_ = lean_ctor_get(v_item_2712_, 2);
lean_inc(v_value_3263_);
lean_dec_ref(v_item_2712_);
v___x_3264_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_value_3263_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_3264_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_2711_);
v_item_2721_ = v_item_2712_;
goto v___jp_2720_;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_item_2712_);
lean_dec_ref(v_config_2711_);
v_a_3265_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_2725_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_2725_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
v___jp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_2723_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_2721_, v___x_2722_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3273_, lean_object* v_item_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(v_config_3273_, v_item_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = lean_box(0);
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_3287_ = l_Lean_mkConst(v___x_3286_, v___x_3285_);
return v___x_3287_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(lean_object* v_cfg_3290_, lean_object* v_cfgItem_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1);
v___x_3300_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3290_, v_cfgItem_3291_, v___x_3299_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_3301_, lean_object* v_cfgItem_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(v_cfg_3301_, v_cfgItem_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_cfgItem_3302_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_cfg_3312_, lean_object* v_init_3313_, uint8_t v_logExceptions_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_onErr_3319_; lean_object* v_eval_3320_; 
v_onErr_3319_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0));
v_eval_3320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_3314_ == 0)
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3320_, v_init_3313_, v_cfg_3312_, v_onErr_3319_, v_logExceptions_3314_, v_a_3316_, v_a_3317_);
return v___x_3321_;
}
else
{
uint8_t v_recover_3322_; lean_object* v___x_3323_; 
v_recover_3322_ = lean_ctor_get_uint8(v_a_3315_, sizeof(void*)*1);
v___x_3323_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3320_, v_init_3313_, v_cfg_3312_, v_onErr_3319_, v_recover_3322_, v_a_3316_, v_a_3317_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_cfg_3324_, lean_object* v_init_3325_, lean_object* v_logExceptions_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
uint8_t v_logExceptions_boxed_3331_; lean_object* v_res_3332_; 
v_logExceptions_boxed_3331_ = lean_unbox(v_logExceptions_3326_);
v_res_3332_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3324_, v_init_3325_, v_logExceptions_boxed_3331_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec_ref(v_a_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_cfg_3333_, lean_object* v_init_3334_, uint8_t v_logExceptions_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3333_, v_init_3334_, v_logExceptions_3335_, v_a_3336_, v_a_3342_, v_a_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_cfg_3346_, lean_object* v_init_3347_, lean_object* v_logExceptions_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_logExceptions_boxed_3358_; lean_object* v_res_3359_; 
v_logExceptions_boxed_3358_ = lean_unbox(v_logExceptions_3348_);
v_res_3359_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_cfg_3346_, v_init_3347_, v_logExceptions_boxed_3358_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_3374_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_3373_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_x_3375_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v___x_3398_ = l_Lean_MVarId_liftLets(v_a_3397_, v_a_3386_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_a_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3401_, v___y_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3402_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3398_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3398_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_a_3386_);
v_a_3411_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3396_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3396_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_3452_, lean_object* v_a_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3455_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_3464_, v_h_3452_, v_a_3453_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_a_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3468_, v___y_3455_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
return v___x_3469_;
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
v_a_3470_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3465_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3465_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_a_3453_);
lean_dec(v_h_3452_);
v_a_3478_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3463_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3463_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_3486_, lean_object* v_a_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_3486_, v_a_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_3498_, lean_object* v_h_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___f_3509_; lean_object* v___x_3510_; 
v___f_3509_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3509_, 0, v_h_3499_);
lean_closure_set(v___f_3509_, 1, v_a_3498_);
v___x_3510_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3509_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_3511_, lean_object* v_h_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_3511_, v_h_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_3530_);
v___x_3541_ = l_Lean_Syntax_isOfKind(v_x_3530_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_x_3530_);
v___x_3542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3543_);
v___x_3545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_3544_);
v___x_3546_ = l_Lean_Syntax_isOfKind(v___x_3544_, v___x_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v___x_3544_);
lean_dec(v_x_3530_);
v___x_3547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3547_;
}
else
{
lean_object* v___f_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v_loc_x3f_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___f_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_3598_ = lean_unsigned_to_nat(2u);
v___x_3599_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3598_);
lean_dec(v_x_3530_);
v___x_3600_ = l_Lean_Syntax_isNone(v___x_3599_);
if (v___x_3600_ == 0)
{
uint8_t v___x_3601_; 
lean_inc(v___x_3599_);
v___x_3601_ = l_Lean_Syntax_matchesNull(v___x_3599_, v___x_3543_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_dec(v___x_3599_);
lean_dec(v___x_3544_);
v___x_3602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3602_;
}
else
{
lean_object* v___x_3603_; lean_object* v_loc_x3f_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3603_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3604_ = l_Lean_Syntax_getArg(v___x_3599_, v___x_3603_);
lean_dec(v___x_3599_);
v___x_3605_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3604_);
v___x_3606_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_loc_x3f_3604_);
lean_dec(v___x_3544_);
v___x_3607_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_loc_x3f_3604_);
v_loc_x3f_3565_ = v___x_3608_;
v___y_3566_ = v_a_3531_;
v___y_3567_ = v_a_3532_;
v___y_3568_ = v_a_3533_;
v___y_3569_ = v_a_3534_;
v___y_3570_ = v_a_3535_;
v___y_3571_ = v_a_3536_;
v___y_3572_ = v_a_3537_;
v___y_3573_ = v_a_3538_;
goto v___jp_3564_;
}
}
}
else
{
lean_object* v___x_3609_; 
lean_dec(v___x_3599_);
v___x_3609_ = lean_box(0);
v_loc_x3f_3565_ = v___x_3609_;
v___y_3566_ = v_a_3531_;
v___y_3567_ = v_a_3532_;
v___y_3568_ = v_a_3533_;
v___y_3569_ = v_a_3534_;
v___y_3570_ = v_a_3535_;
v___y_3571_ = v_a_3536_;
v___y_3572_ = v_a_3537_;
v___y_3573_ = v_a_3538_;
goto v___jp_3564_;
}
v___jp_3549_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = l_Lean_mkOptionalNode(v___y_3560_);
v___x_3562_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3561_);
lean_dec(v___x_3561_);
v___x_3563_ = l_Lean_Elab_Tactic_withLocation(v___x_3562_, v___y_3552_, v___y_3550_, v___f_3548_, v___y_3559_, v___y_3555_, v___y_3553_, v___y_3558_, v___y_3556_, v___y_3557_, v___y_3554_, v___y_3551_);
lean_dec(v___x_3562_);
return v___x_3563_;
}
v___jp_3564_:
{
uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = 0;
v___x_3575_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_3575_, 0, v___x_3574_);
lean_ctor_set_uint8(v___x_3575_, 1, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 2, v___x_3574_);
lean_ctor_set_uint8(v___x_3575_, 3, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 4, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 5, v___x_3574_);
lean_ctor_set_uint8(v___x_3575_, 6, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 7, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 8, v___x_3574_);
lean_ctor_set_uint8(v___x_3575_, 9, v___x_3546_);
lean_ctor_set_uint8(v___x_3575_, 10, v___x_3546_);
v___x_3576_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_3544_, v___x_3575_, v___x_3546_, v___y_3566_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc_n(v_a_3577_, 2);
lean_dec_ref_known(v___x_3576_, 1);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3578_, 0, v_a_3577_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3579_, 0, v___f_3578_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_3580_, 0, v_a_3577_);
if (lean_obj_tag(v_loc_x3f_3565_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_box(0);
v___y_3550_ = v___f_3579_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___f_3580_;
v___y_3553_ = v___y_3568_;
v___y_3554_ = v___y_3572_;
v___y_3555_ = v___y_3567_;
v___y_3556_ = v___y_3570_;
v___y_3557_ = v___y_3571_;
v___y_3558_ = v___y_3569_;
v___y_3559_ = v___y_3566_;
v___y_3560_ = v___x_3581_;
goto v___jp_3549_;
}
else
{
lean_object* v_val_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
v_val_3582_ = lean_ctor_get(v_loc_x3f_3565_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_loc_x3f_3565_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v_loc_x3f_3565_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_val_3582_);
lean_dec(v_loc_x3f_3565_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_val_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
v___y_3550_ = v___f_3579_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___f_3580_;
v___y_3553_ = v___y_3568_;
v___y_3554_ = v___y_3572_;
v___y_3555_ = v___y_3567_;
v___y_3556_ = v___y_3570_;
v___y_3557_ = v___y_3571_;
v___y_3558_ = v___y_3569_;
v___y_3559_ = v___y_3566_;
v___y_3560_ = v___x_3587_;
goto v___jp_3549_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_loc_x3f_3565_);
v_a_3590_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3576_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3576_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3628_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3629_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_3630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_3631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_3632_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3628_, v___x_3629_, v___x_3630_, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_3637_ = l_Lean_stringToMessageData(v___x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_3649_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_3648_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_x_3650_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t v___x_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3663_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___x_3673_ = l_Lean_MVarId_letToHave(v_a_3672_, v___x_3661_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v___x_3675_ = lean_box(0);
v___x_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3676_, 0, v_a_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3676_, v___y_3663_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
return v___x_3677_;
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
v_a_3678_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3673_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3673_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3671_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3671_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v___x_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v___x_1036__boxed_3704_; lean_object* v_res_3705_; 
v___x_1036__boxed_3704_ = lean_unbox(v___x_3694_);
v_res_3705_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v___x_1036__boxed_3704_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object* v_h_3706_, uint8_t v___x_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3709_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_3718_, v_h_3706_, v___x_3707_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___x_3721_ = lean_box(0);
v___x_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_a_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3722_, v___y_3709_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3723_;
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_a_3724_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3719_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3719_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_h_3706_);
v_a_3732_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3717_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3717_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v_h_3740_, lean_object* v___x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v___x_1112__boxed_3751_; lean_object* v_res_3752_; 
v___x_1112__boxed_3751_ = lean_unbox(v___x_3741_);
v_res_3752_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v_h_3740_, v___x_1112__boxed_3751_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_3753_, lean_object* v_h_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_box(v___x_3753_);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3765_, 0, v_h_3754_);
lean_closure_set(v___f_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3765_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_3767_, lean_object* v_h_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
uint8_t v___x_1188__boxed_3778_; lean_object* v_res_3779_; 
v___x_1188__boxed_3778_ = lean_unbox(v___x_3767_);
v_res_3779_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1188__boxed_3778_, v_h_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_3787_);
v___x_3798_ = l_Lean_Syntax_isOfKind(v_x_3787_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_x_3787_);
v___x_3799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3799_;
}
else
{
lean_object* v___f_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___f_3803_; lean_object* v___x_3804_; lean_object* v___f_3805_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___f_3800_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_3801_ = lean_box(v___x_3798_);
v___f_3802_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3802_, 0, v___x_3801_);
v___f_3803_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3803_, 0, v___f_3802_);
v___x_3804_ = lean_box(v___x_3798_);
v___f_3805_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_3805_, 0, v___x_3804_);
v___x_3819_ = lean_unsigned_to_nat(1u);
v___x_3820_ = l_Lean_Syntax_getArg(v_x_3787_, v___x_3819_);
lean_dec(v_x_3787_);
v___x_3821_ = l_Lean_Syntax_isNone(v___x_3820_);
if (v___x_3821_ == 0)
{
uint8_t v___x_3822_; 
lean_inc(v___x_3820_);
v___x_3822_ = l_Lean_Syntax_matchesNull(v___x_3820_, v___x_3819_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
lean_dec(v___x_3820_);
lean_dec_ref(v___f_3805_);
lean_dec_ref(v___f_3803_);
v___x_3823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; lean_object* v_loc_x3f_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3824_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3825_ = l_Lean_Syntax_getArg(v___x_3820_, v___x_3824_);
lean_dec(v___x_3820_);
v___x_3826_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3825_);
v___x_3827_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3825_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec(v_loc_x3f_3825_);
lean_dec_ref(v___f_3805_);
lean_dec_ref(v___f_3803_);
v___x_3828_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3828_;
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_loc_x3f_3825_);
v___y_3807_ = v_a_3791_;
v___y_3808_ = v_a_3793_;
v___y_3809_ = v_a_3792_;
v___y_3810_ = v_a_3788_;
v___y_3811_ = v_a_3789_;
v___y_3812_ = v_a_3795_;
v___y_3813_ = v_a_3794_;
v___y_3814_ = v_a_3790_;
v___y_3815_ = v___x_3829_;
goto v___jp_3806_;
}
}
}
else
{
lean_object* v___x_3830_; 
lean_dec(v___x_3820_);
v___x_3830_ = lean_box(0);
v___y_3807_ = v_a_3791_;
v___y_3808_ = v_a_3793_;
v___y_3809_ = v_a_3792_;
v___y_3810_ = v_a_3788_;
v___y_3811_ = v_a_3789_;
v___y_3812_ = v_a_3795_;
v___y_3813_ = v_a_3794_;
v___y_3814_ = v_a_3790_;
v___y_3815_ = v___x_3830_;
goto v___jp_3806_;
}
v___jp_3806_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = l_Lean_mkOptionalNode(v___y_3815_);
v___x_3817_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3816_);
lean_dec(v___x_3816_);
v___x_3818_ = l_Lean_Elab_Tactic_withLocation(v___x_3817_, v___f_3805_, v___f_3803_, v___f_3800_, v___y_3810_, v___y_3811_, v___y_3814_, v___y_3807_, v___y_3809_, v___y_3808_, v___y_3813_, v___y_3812_);
lean_dec(v___x_3817_);
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3849_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3850_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_3851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_3852_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_3853_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3849_, v___x_3850_, v___x_3851_, v___x_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_3855_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_linter_tactic_unusedName = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_linter_tactic_unusedName);
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig = _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig);
res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig = _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig);
res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
