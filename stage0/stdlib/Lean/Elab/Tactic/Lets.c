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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_value;
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "'extract_lets' tactic failed"};
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 187, 108, 174, 23, 225, 147, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_value;
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
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "'lift_lets' tactic failed"};
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
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "'let_to_have' tactic failed"};
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
lean_object* v___x_84_; lean_object* v_env_85_; lean_object* v___x_86_; lean_object* v_mctx_87_; lean_object* v_lctx_88_; lean_object* v_options_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_84_ = lean_st_ref_get(v___y_82_);
v_env_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_84_);
v___x_86_ = lean_st_ref_get(v___y_80_);
v_mctx_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_mctx_87_);
lean_dec(v___x_86_);
v_lctx_88_ = lean_ctor_get(v___y_79_, 2);
v_options_89_ = lean_ctor_get(v___y_81_, 2);
lean_inc_ref(v_options_89_);
lean_inc_ref(v_lctx_88_);
v___x_90_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_90_, 0, v_env_85_);
lean_ctor_set(v___x_90_, 1, v_mctx_87_);
lean_ctor_set(v___x_90_, 2, v_lctx_88_);
lean_ctor_set(v___x_90_, 3, v_options_89_);
v___x_91_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_msgData_78_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msgData_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msgData_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t v___y_106_, uint8_t v_suppressElabErrors_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 1)
{
lean_object* v_pre_109_; 
v_pre_109_ = lean_ctor_get(v_x_108_, 0);
switch(lean_obj_tag(v_pre_109_))
{
case 1:
{
lean_object* v_pre_110_; 
v_pre_110_ = lean_ctor_get(v_pre_109_, 0);
switch(lean_obj_tag(v_pre_110_))
{
case 0:
{
lean_object* v_str_111_; lean_object* v_str_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_str_111_ = lean_ctor_get(v_x_108_, 1);
v_str_112_ = lean_ctor_get(v_pre_109_, 1);
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_114_ = lean_string_dec_eq(v_str_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_116_ = lean_string_dec_eq(v_str_112_, v___x_115_);
if (v___x_116_ == 0)
{
return v___y_106_;
}
else
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_118_ = lean_string_dec_eq(v_str_111_, v___x_117_);
if (v___x_118_ == 0)
{
return v___y_106_;
}
else
{
return v_suppressElabErrors_107_;
}
}
}
else
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_120_ = lean_string_dec_eq(v_str_111_, v___x_119_);
if (v___x_120_ == 0)
{
return v___y_106_;
}
else
{
return v_suppressElabErrors_107_;
}
}
}
case 1:
{
lean_object* v_pre_121_; 
v_pre_121_ = lean_ctor_get(v_pre_110_, 0);
if (lean_obj_tag(v_pre_121_) == 0)
{
lean_object* v_str_122_; lean_object* v_str_123_; lean_object* v_str_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_str_122_ = lean_ctor_get(v_x_108_, 1);
v_str_123_ = lean_ctor_get(v_pre_109_, 1);
v_str_124_ = lean_ctor_get(v_pre_110_, 1);
v___x_125_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_126_ = lean_string_dec_eq(v_str_124_, v___x_125_);
if (v___x_126_ == 0)
{
return v___y_106_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_128_ = lean_string_dec_eq(v_str_123_, v___x_127_);
if (v___x_128_ == 0)
{
return v___y_106_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_130_ = lean_string_dec_eq(v_str_122_, v___x_129_);
if (v___x_130_ == 0)
{
return v___y_106_;
}
else
{
return v_suppressElabErrors_107_;
}
}
}
}
else
{
return v___y_106_;
}
}
default: 
{
return v___y_106_;
}
}
}
case 0:
{
lean_object* v_str_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_str_131_ = lean_ctor_get(v_x_108_, 1);
v___x_132_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_133_ = lean_string_dec_eq(v_str_131_, v___x_132_);
if (v___x_133_ == 0)
{
return v___y_106_;
}
else
{
return v_suppressElabErrors_107_;
}
}
default: 
{
return v___y_106_;
}
}
}
else
{
return v___y_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_134_, lean_object* v_suppressElabErrors_135_, lean_object* v_x_136_){
_start:
{
uint8_t v___y_6520__boxed_137_; uint8_t v_suppressElabErrors_boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v___y_6520__boxed_137_ = lean_unbox(v___y_134_);
v_suppressElabErrors_boxed_138_ = lean_unbox(v_suppressElabErrors_135_);
v_res_139_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v___y_6520__boxed_137_, v_suppressElabErrors_boxed_138_, v_x_136_);
lean_dec(v_x_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_142_, lean_object* v_msgData_143_, uint8_t v_severity_144_, uint8_t v_isSilent_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___y_192_; uint8_t v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___y_217_; uint8_t v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___x_235_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; uint8_t v___y_243_; uint8_t v___y_245_; uint8_t v___x_260_; 
v___x_235_ = 2;
v___x_260_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_235_);
if (v___x_260_ == 0)
{
v___y_245_ = v___x_260_;
goto v___jp_244_;
}
else
{
uint8_t v___x_261_; 
lean_inc_ref(v_msgData_143_);
v___x_261_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_143_);
v___y_245_ = v___x_261_;
goto v___jp_244_;
}
v___jp_151_:
{
lean_object* v___x_161_; lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v_env_164_; lean_object* v_nextMacroScope_165_; lean_object* v_ngen_166_; lean_object* v_auxDeclNGen_167_; lean_object* v_traceState_168_; lean_object* v_cache_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_186_; 
v___x_161_ = lean_st_ref_take(v___y_160_);
v_currNamespace_162_ = lean_ctor_get(v___y_159_, 6);
v_openDecls_163_ = lean_ctor_get(v___y_159_, 7);
v_env_164_ = lean_ctor_get(v___x_161_, 0);
v_nextMacroScope_165_ = lean_ctor_get(v___x_161_, 1);
v_ngen_166_ = lean_ctor_get(v___x_161_, 2);
v_auxDeclNGen_167_ = lean_ctor_get(v___x_161_, 3);
v_traceState_168_ = lean_ctor_get(v___x_161_, 4);
v_cache_169_ = lean_ctor_get(v___x_161_, 5);
v_messages_170_ = lean_ctor_get(v___x_161_, 6);
v_infoState_171_ = lean_ctor_get(v___x_161_, 7);
v_snapshotTasks_172_ = lean_ctor_get(v___x_161_, 8);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_186_ == 0)
{
v___x_174_ = v___x_161_;
v_isShared_175_ = v_isSharedCheck_186_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_snapshotTasks_172_);
lean_inc(v_infoState_171_);
lean_inc(v_messages_170_);
lean_inc(v_cache_169_);
lean_inc(v_traceState_168_);
lean_inc(v_auxDeclNGen_167_);
lean_inc(v_ngen_166_);
lean_inc(v_nextMacroScope_165_);
lean_inc(v_env_164_);
lean_dec(v___x_161_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_186_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_inc(v_openDecls_163_);
lean_inc(v_currNamespace_162_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v_currNamespace_162_);
lean_ctor_set(v___x_176_, 1, v_openDecls_163_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc_ref(v___y_154_);
v___x_178_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_178_, 0, v___y_154_);
lean_ctor_set(v___x_178_, 1, v___y_155_);
lean_ctor_set(v___x_178_, 2, v___y_157_);
lean_ctor_set(v___x_178_, 3, v___y_152_);
lean_ctor_set(v___x_178_, 4, v___x_177_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5, v___y_156_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5 + 1, v___y_158_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5 + 2, v_isSilent_145_);
v___x_179_ = l_Lean_MessageLog_add(v___x_178_, v_messages_170_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 6, v___x_179_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_env_164_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_nextMacroScope_165_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_ngen_166_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_auxDeclNGen_167_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_traceState_168_);
lean_ctor_set(v_reuseFailAlloc_185_, 5, v_cache_169_);
lean_ctor_set(v_reuseFailAlloc_185_, 6, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_185_, 7, v_infoState_171_);
lean_ctor_set(v_reuseFailAlloc_185_, 8, v_snapshotTasks_172_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_st_ref_set(v___y_160_, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
v___jp_187_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_211_; 
v___x_196_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_143_);
v___x_197_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_196_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_211_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc_ref_n(v___y_189_, 2);
v___x_202_ = l_Lean_FileMap_toPosition(v___y_189_, v___y_191_);
lean_dec(v___y_191_);
v___x_203_ = l_Lean_FileMap_toPosition(v___y_189_, v___y_195_);
lean_dec(v___y_195_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_192_ == 0)
{
lean_del_object(v___x_200_);
lean_dec_ref(v___y_188_);
v___y_152_ = v___x_205_;
v___y_153_ = v_a_198_;
v___y_154_ = v___y_190_;
v___y_155_ = v___x_202_;
v___y_156_ = v___y_193_;
v___y_157_ = v___x_204_;
v___y_158_ = v___y_194_;
v___y_159_ = v___y_148_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
else
{
uint8_t v___x_206_; 
lean_inc(v_a_198_);
v___x_206_ = l_Lean_MessageData_hasTag(v___y_188_, v_a_198_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec_ref_known(v___x_204_, 1);
lean_dec_ref(v___x_202_);
lean_dec(v_a_198_);
v___x_207_ = lean_box(0);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_207_);
v___x_209_ = v___x_200_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
else
{
lean_del_object(v___x_200_);
v___y_152_ = v___x_205_;
v___y_153_ = v_a_198_;
v___y_154_ = v___y_190_;
v___y_155_ = v___x_202_;
v___y_156_ = v___y_193_;
v___y_157_ = v___x_204_;
v___y_158_ = v___y_194_;
v___y_159_ = v___y_148_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
}
}
}
v___jp_212_:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_215_, v___y_218_);
lean_dec(v___y_215_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_188_ = v___y_213_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_216_;
v___y_191_ = v___y_220_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
v___y_195_ = v___y_220_;
goto v___jp_187_;
}
else
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___y_188_ = v___y_213_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_216_;
v___y_191_ = v___y_220_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
v___y_195_ = v_val_222_;
goto v___jp_187_;
}
}
v___jp_223_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = l_Lean_replaceRef(v_ref_142_, v___y_227_);
v___x_232_ = l_Lean_Syntax_getPos_x3f(v_ref_231_, v___y_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_213_ = v___y_224_;
v___y_214_ = v___y_225_;
v___y_215_ = v_ref_231_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_230_;
v___y_220_ = v___x_233_;
goto v___jp_212_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v___y_213_ = v___y_224_;
v___y_214_ = v___y_225_;
v___y_215_ = v_ref_231_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_230_;
v___y_220_ = v_val_234_;
goto v___jp_212_;
}
}
v___jp_236_:
{
if (v___y_243_ == 0)
{
v___y_224_ = v___y_241_;
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_242_;
v___y_230_ = v_severity_144_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_241_;
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_242_;
v___y_230_ = v___x_235_;
goto v___jp_223_;
}
}
v___jp_244_:
{
if (v___y_245_ == 0)
{
lean_object* v_fileName_246_; lean_object* v_fileMap_247_; lean_object* v_options_248_; lean_object* v_ref_249_; uint8_t v_suppressElabErrors_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___f_253_; uint8_t v___x_254_; uint8_t v___x_255_; 
v_fileName_246_ = lean_ctor_get(v___y_148_, 0);
v_fileMap_247_ = lean_ctor_get(v___y_148_, 1);
v_options_248_ = lean_ctor_get(v___y_148_, 2);
v_ref_249_ = lean_ctor_get(v___y_148_, 5);
v_suppressElabErrors_250_ = lean_ctor_get_uint8(v___y_148_, sizeof(void*)*14 + 1);
v___x_251_ = lean_box(v___y_245_);
v___x_252_ = lean_box(v_suppressElabErrors_250_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_253_, 0, v___x_251_);
lean_closure_set(v___f_253_, 1, v___x_252_);
v___x_254_ = 1;
v___x_255_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_254_);
if (v___x_255_ == 0)
{
v___y_237_ = v_fileMap_247_;
v___y_238_ = v_fileName_246_;
v___y_239_ = v_ref_249_;
v___y_240_ = v_suppressElabErrors_250_;
v___y_241_ = v___f_253_;
v___y_242_ = v___y_245_;
v___y_243_ = v___x_255_;
goto v___jp_236_;
}
else
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = l_Lean_warningAsError;
v___x_257_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_248_, v___x_256_);
v___y_237_ = v_fileMap_247_;
v___y_238_ = v_fileName_246_;
v___y_239_ = v_ref_249_;
v___y_240_ = v_suppressElabErrors_250_;
v___y_241_ = v___f_253_;
v___y_242_ = v___y_245_;
v___y_243_ = v___x_257_;
goto v___jp_236_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v_msgData_143_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_262_, lean_object* v_msgData_263_, lean_object* v_severity_264_, lean_object* v_isSilent_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v_severity_boxed_271_; uint8_t v_isSilent_boxed_272_; lean_object* v_res_273_; 
v_severity_boxed_271_ = lean_unbox(v_severity_264_);
v_isSilent_boxed_272_ = lean_unbox(v_isSilent_265_);
v_res_273_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_262_, v_msgData_263_, v_severity_boxed_271_, v_isSilent_boxed_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v_ref_262_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object* v_ref_274_, lean_object* v_msgData_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
uint8_t v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 1;
v___x_286_ = 0;
v___x_287_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_274_, v_msgData_275_, v___x_285_, v___x_286_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object* v_ref_288_, lean_object* v_msgData_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_288_, v_msgData_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v_ref_288_);
return v_res_299_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object* v_linterOption_306_, lean_object* v_stx_307_, lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_name_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_336_; 
v_name_318_ = lean_ctor_get(v_linterOption_306_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_linterOption_306_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_linterOption_306_, 1);
lean_dec(v_unused_337_);
v___x_320_ = v_linterOption_306_;
v_isShared_321_ = v_isSharedCheck_336_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_name_318_);
lean_dec(v_linterOption_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_336_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
lean_inc(v_name_318_);
v___x_323_ = l_Lean_MessageData_ofName(v_name_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 7);
lean_ctor_set(v___x_320_, 1, v___x_323_);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_335_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_disable_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v_disable_328_ = l_Lean_MessageData_note(v___x_327_);
v___x_329_ = l_Lean_Linter_linterMessageTag;
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v_msg_308_);
lean_ctor_set(v___x_330_, 1, v_disable_328_);
v___x_331_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_332_, 0, v_name_318_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_inc(v_stx_307_);
v___x_333_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_333_, 0, v_stx_307_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_307_, v___x_333_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v_stx_307_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object* v_linterOption_338_, lean_object* v_stx_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_338_, v_stx_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v_env_355_; lean_object* v___x_356_; lean_object* v_toEnvExtension_357_; lean_object* v_asyncMode_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_merged_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v___x_354_ = lean_st_ref_get(v___y_352_);
v_env_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_ref(v_env_355_);
lean_dec(v___x_354_);
v___x_356_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_357_ = lean_ctor_get(v___x_356_, 0);
v_asyncMode_358_ = lean_ctor_get(v_toEnvExtension_357_, 2);
v___x_359_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_360_ = lean_box(0);
v___x_361_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_359_, v___x_356_, v_env_355_, v_asyncMode_358_, v___x_360_);
v_merged_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_361_, 1);
lean_dec(v_unused_371_);
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_merged_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_merged_362_);
lean_ctor_set(v___x_364_, 0, v_o_351_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_o_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_merged_362_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_372_, v___y_373_);
lean_dec(v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_options_385_; lean_object* v___x_386_; 
v_options_385_ = lean_ctor_get(v___y_382_, 2);
lean_inc_ref(v_options_385_);
v___x_386_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_385_, v___y_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_397_, lean_object* v_stx_398_, lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_420_; 
v___x_409_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_420_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; 
v___x_414_ = l_Lean_Linter_getLinterValue(v_linterOption_397_, v_a_410_);
lean_dec(v_a_410_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec_ref(v_msg_399_);
lean_dec(v_stx_398_);
lean_dec_ref(v_linterOption_397_);
v___x_415_ = lean_box(0);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v___x_419_; 
lean_del_object(v___x_412_);
v___x_419_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_397_, v_stx_398_, v_msg_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_421_, lean_object* v_stx_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_421_, v_stx_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_433_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_437_, lean_object* v_fvars_438_, lean_object* v_ids_439_, lean_object* v_a_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_a_452_; uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_lt(v_a_440_, v_upperBound_437_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v_a_440_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_b_441_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_array_get_size(v_fvars_438_);
v___x_460_ = lean_nat_dec_lt(v_a_440_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_462_ = lean_array_fget_borrowed(v_ids_439_, v_a_440_);
v___x_463_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
lean_inc(v___x_462_);
v___x_464_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_461_, v___x_462_, v___x_463_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v_a_452_ = v___x_458_;
goto v___jp_451_;
}
else
{
lean_dec(v_a_440_);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_465_ = lean_array_fget_borrowed(v_ids_439_, v_a_440_);
v___x_466_ = lean_array_fget_borrowed(v_fvars_438_, v_a_440_);
lean_inc(v___x_466_);
v___x_467_ = l_Lean_mkFVar(v___x_466_);
lean_inc(v___x_465_);
v___x_468_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_465_, v___x_467_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref_known(v___x_468_, 1);
v_a_452_ = v___x_458_;
goto v___jp_451_;
}
else
{
lean_dec(v_a_440_);
return v___x_468_;
}
}
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_a_440_, v___x_453_);
lean_dec(v_a_440_);
v_a_440_ = v___x_454_;
v_b_441_ = v_a_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_469_, lean_object* v_fvars_470_, lean_object* v_ids_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_469_, v_fvars_470_, v_ids_471_, v_a_472_, v_b_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec_ref(v_ids_471_);
lean_dec_ref(v_fvars_470_);
lean_dec(v_upperBound_469_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_484_, lean_object* v_fvars_485_, lean_object* v_ids_486_, lean_object* v___x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_484_, v_fvars_485_, v_ids_486_, v___x_497_, v___x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_506_);
v___x_500_ = v___x_498_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_498_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_487_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_487_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_507_, lean_object* v_fvars_508_, lean_object* v_ids_509_, lean_object* v___x_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_507_, v_fvars_508_, v_ids_509_, v___x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_ids_509_);
lean_dec_ref(v_fvars_508_);
lean_dec(v___x_507_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_521_, lean_object* v_fvars_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
v___x_532_ = lean_array_get_size(v_ids_521_);
v___x_533_ = lean_box(0);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_534_, 0, v___x_532_);
lean_closure_set(v___f_534_, 1, v_fvars_522_);
lean_closure_set(v___f_534_, 2, v_ids_521_);
lean_closure_set(v___f_534_, 3, v___x_533_);
v___x_535_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_534_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_536_, lean_object* v_fvars_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_536_, v_fvars_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_548_, lean_object* v_fvars_549_, lean_object* v_ids_550_, lean_object* v_inst_551_, lean_object* v_R_552_, lean_object* v_a_553_, lean_object* v_b_554_, lean_object* v_c_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_548_, v_fvars_549_, v_ids_550_, v_a_553_, v_b_554_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_566_ = _args[0];
lean_object* v_fvars_567_ = _args[1];
lean_object* v_ids_568_ = _args[2];
lean_object* v_inst_569_ = _args[3];
lean_object* v_R_570_ = _args[4];
lean_object* v_a_571_ = _args[5];
lean_object* v_b_572_ = _args[6];
lean_object* v_c_573_ = _args[7];
lean_object* v___y_574_ = _args[8];
lean_object* v___y_575_ = _args[9];
lean_object* v___y_576_ = _args[10];
lean_object* v___y_577_ = _args[11];
lean_object* v___y_578_ = _args[12];
lean_object* v___y_579_ = _args[13];
lean_object* v___y_580_ = _args[14];
lean_object* v___y_581_ = _args[15];
lean_object* v___y_582_ = _args[16];
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_566_, v_fvars_567_, v_ids_568_, v_inst_569_, v_R_570_, v_a_571_, v_b_572_, v_c_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_ids_568_);
lean_dec_ref(v_fvars_567_);
lean_dec(v_upperBound_566_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_584_, v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_606_, lean_object* v_msgData_607_, uint8_t v_severity_608_, uint8_t v_isSilent_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_606_, v_msgData_607_, v_severity_608_, v_isSilent_609_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_620_, lean_object* v_msgData_621_, lean_object* v_severity_622_, lean_object* v_isSilent_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v_severity_boxed_633_; uint8_t v_isSilent_boxed_634_; lean_object* v_res_635_; 
v_severity_boxed_633_ = lean_unbox(v_severity_622_);
v_isSilent_boxed_634_ = lean_unbox(v_isSilent_623_);
v_res_635_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_620_, v_msgData_621_, v_severity_boxed_633_, v_isSilent_boxed_634_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v_ref_620_);
return v_res_635_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(lean_object* v_00_u03b1_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(v_00_u03b1_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_ref_664_ = lean_ctor_get(v___y_661_, 5);
v___x_665_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_inc(v_ref_664_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_ref_664_);
lean_ctor_set(v___x_670_, 1, v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 1);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object* v_ctor_686_, lean_object* v_args_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_847_ = lean_string_dec_eq(v_ctor_686_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_array_get_size(v_args_687_);
v___x_850_ = lean_unsigned_to_nat(11u);
v___x_851_ = lean_nat_dec_eq(v___x_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v___x_852_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_853_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_852_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
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
else
{
goto v___jp_693_;
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = l_Lean_instInhabitedExpr;
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_695_);
lean_inc(v___x_696_);
v___x_697_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_696_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_699_);
lean_inc(v___x_700_);
v___x_701_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_700_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_unsigned_to_nat(2u);
v___x_704_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_703_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_704_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_unsigned_to_nat(3u);
v___x_708_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_707_);
lean_inc(v___x_708_);
v___x_709_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_708_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_711_);
lean_inc(v___x_712_);
v___x_713_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_712_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = lean_unsigned_to_nat(5u);
v___x_716_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_715_);
lean_inc(v___x_716_);
v___x_717_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_716_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_unsigned_to_nat(6u);
v___x_720_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_719_);
lean_inc(v___x_720_);
v___x_721_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_720_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_unsigned_to_nat(7u);
v___x_724_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_723_);
lean_inc(v___x_724_);
v___x_725_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_724_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_unsigned_to_nat(8u);
v___x_728_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_727_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_728_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = lean_unsigned_to_nat(9u);
v___x_732_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_731_);
lean_inc(v___x_732_);
v___x_733_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_732_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_unsigned_to_nat(10u);
v___x_736_ = lean_array_get_borrowed(v___x_694_, v_args_687_, v___x_735_);
lean_inc(v___x_736_);
v___x_737_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_736_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_757_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_757_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_757_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_757_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; uint8_t v___x_750_; uint8_t v___x_751_; uint8_t v___x_752_; uint8_t v___x_753_; lean_object* v___x_755_; 
v___x_742_ = lean_alloc_ctor(0, 0, 11);
v___x_743_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
lean_ctor_set_uint8(v___x_742_, 0, v___x_743_);
v___x_744_ = lean_unbox(v_a_702_);
lean_dec(v_a_702_);
lean_ctor_set_uint8(v___x_742_, 1, v___x_744_);
v___x_745_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
lean_ctor_set_uint8(v___x_742_, 2, v___x_745_);
v___x_746_ = lean_unbox(v_a_710_);
lean_dec(v_a_710_);
lean_ctor_set_uint8(v___x_742_, 3, v___x_746_);
v___x_747_ = lean_unbox(v_a_714_);
lean_dec(v_a_714_);
lean_ctor_set_uint8(v___x_742_, 4, v___x_747_);
v___x_748_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
lean_ctor_set_uint8(v___x_742_, 5, v___x_748_);
v___x_749_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
lean_ctor_set_uint8(v___x_742_, 6, v___x_749_);
v___x_750_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
lean_ctor_set_uint8(v___x_742_, 7, v___x_750_);
v___x_751_ = lean_unbox(v_a_730_);
lean_dec(v_a_730_);
lean_ctor_set_uint8(v___x_742_, 8, v___x_751_);
v___x_752_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
lean_ctor_set_uint8(v___x_742_, 9, v___x_752_);
v___x_753_ = lean_unbox(v_a_738_);
lean_dec(v_a_738_);
lean_ctor_set_uint8(v___x_742_, 10, v___x_753_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_755_ = v___x_740_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_742_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_734_);
lean_dec(v_a_730_);
lean_dec(v_a_726_);
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_758_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_737_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_737_);
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
lean_dec(v_a_730_);
lean_dec(v_a_726_);
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_766_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_733_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_733_);
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
lean_dec(v_a_726_);
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_774_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_729_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_729_);
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
lean_dec(v_a_722_);
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_782_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_725_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_725_);
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
lean_dec(v_a_718_);
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_790_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_721_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_721_);
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
lean_dec(v_a_714_);
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_798_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_717_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_717_);
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
lean_dec(v_a_710_);
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_806_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_713_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_713_);
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
lean_dec(v_a_706_);
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_814_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_709_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_709_);
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
lean_dec(v_a_702_);
lean_dec(v_a_698_);
v_a_822_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_705_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_705_);
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
lean_dec(v_a_698_);
v_a_830_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_701_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_701_);
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
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_697_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_697_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_862_, lean_object* v_args_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(v_ctor_862_, v_args_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_args_863_);
lean_dec_ref(v_ctor_862_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___f_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0));
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_885_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_884_, v___f_883_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(lean_object* v_00_u03b1_893_, lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_901_, lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(v_00_u03b1_901_, v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_box(0);
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_912_ = l_Lean_Expr_const___override(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0));
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig(void){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; uint8_t v___x_923_; 
v___x_922_ = l_Lean_Expr_hasMVar(v_e_919_);
v___x_923_ = lean_bool_not(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v___x_926_; lean_object* v_fst_927_; lean_object* v_snd_928_; lean_object* v___x_929_; lean_object* v_cache_930_; lean_object* v_zetaDeltaFVarIds_931_; lean_object* v_postponed_932_; lean_object* v_diag_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_942_; 
v___x_924_ = lean_st_ref_get(v___y_920_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_mctx_925_);
lean_dec(v___x_924_);
v___x_926_ = l_Lean_instantiateMVarsCore(v_mctx_925_, v_e_919_);
v_fst_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_fst_927_);
v_snd_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v___x_926_);
v___x_929_ = lean_st_ref_take(v___y_920_);
v_cache_930_ = lean_ctor_get(v___x_929_, 1);
v_zetaDeltaFVarIds_931_ = lean_ctor_get(v___x_929_, 2);
v_postponed_932_ = lean_ctor_get(v___x_929_, 3);
v_diag_933_ = lean_ctor_get(v___x_929_, 4);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_943_);
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_diag_933_);
lean_inc(v_postponed_932_);
lean_inc(v_zetaDeltaFVarIds_931_);
lean_inc(v_cache_930_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_snd_928_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_snd_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_cache_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_zetaDeltaFVarIds_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_postponed_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_diag_933_);
v___x_938_ = v_reuseFailAlloc_941_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_st_ref_set(v___y_920_, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_fst_927_);
return v___x_940_;
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_e_919_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_945_, v___y_946_);
lean_dec(v___y_946_);
return v_res_948_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_box(1);
v___x_950_ = l_Lean_MessageData_ofFormat(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2));
v___x_955_ = l_Lean_MessageData_ofFormat(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
if (lean_obj_tag(v_x_957_) == 0)
{
return v_x_956_;
}
else
{
lean_object* v_head_958_; lean_object* v_tail_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_981_; 
v_head_958_ = lean_ctor_get(v_x_957_, 0);
v_tail_959_ = lean_ctor_get(v_x_957_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_957_);
if (v_isSharedCheck_981_ == 0)
{
v___x_961_ = v_x_957_;
v_isShared_962_ = v_isSharedCheck_981_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_tail_959_);
lean_inc(v_head_958_);
lean_dec(v_x_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_981_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_before_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_979_; 
v_before_963_ = lean_ctor_get(v_head_958_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_head_958_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_head_958_, 1);
lean_dec(v_unused_980_);
v___x_965_ = v_head_958_;
v_isShared_966_ = v_isSharedCheck_979_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_before_963_);
lean_dec(v_head_958_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_979_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 7);
lean_ctor_set(v___x_965_, 1, v___x_967_);
lean_ctor_set(v___x_965_, 0, v_x_956_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_x_956_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_978_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 7);
lean_ctor_set(v___x_961_, 1, v___x_970_);
lean_ctor_set(v___x_961_, 0, v___x_969_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_977_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = l_Lean_MessageData_ofSyntax(v_before_963_);
v___x_974_ = l_Lean_indentD(v___x_973_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_972_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v_x_956_ = v___x_975_;
v_x_957_ = v_tail_959_;
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
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_986_ = l_Lean_MessageData_ofFormat(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_987_, lean_object* v_macroStack_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_options_991_; lean_object* v___x_992_; uint8_t v___x_993_; uint8_t v___x_994_; 
v_options_991_ = lean_ctor_get(v___y_989_, 2);
v___x_992_ = l_Lean_Elab_pp_macroStack;
v___x_993_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_991_, v___x_992_);
v___x_994_ = lean_bool_not(v___x_993_);
if (v___x_994_ == 0)
{
if (lean_obj_tag(v_macroStack_988_) == 0)
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v_msgData_987_);
return v___x_995_;
}
else
{
lean_object* v_head_996_; lean_object* v_after_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1012_; 
v_head_996_ = lean_ctor_get(v_macroStack_988_, 0);
lean_inc(v_head_996_);
v_after_997_ = lean_ctor_get(v_head_996_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_head_996_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_head_996_, 0);
lean_dec(v_unused_1013_);
v___x_999_ = v_head_996_;
v_isShared_1000_ = v_isSharedCheck_1012_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_after_997_);
lean_dec(v_head_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1012_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 7);
lean_ctor_set(v___x_999_, 1, v___x_1001_);
lean_ctor_set(v___x_999_, 0, v_msgData_987_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_msgData_987_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_msgData_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1004_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_MessageData_ofSyntax(v_after_997_);
v___x_1007_ = l_Lean_indentD(v___x_1006_);
v_msgData_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1008_, 0, v___x_1005_);
lean_ctor_set(v_msgData_1008_, 1, v___x_1007_);
v___x_1009_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_msgData_1008_, v_macroStack_988_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
}
else
{
lean_object* v___x_1014_; 
lean_dec(v_macroStack_988_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_msgData_987_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1015_, lean_object* v_macroStack_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1015_, v_macroStack_1016_, v___y_1017_);
lean_dec_ref(v___y_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_ref_1028_; lean_object* v___x_1029_; lean_object* v_a_1030_; lean_object* v_macroStack_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_ref_1028_ = lean_ctor_get(v___y_1025_, 5);
v___x_1029_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1020_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v_macroStack_1031_ = lean_ctor_get(v___y_1021_, 1);
v___x_1032_ = l_Lean_Elab_getBetterRef(v_ref_1028_, v_macroStack_1031_);
lean_inc(v_macroStack_1031_);
v___x_1033_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_1030_, v_macroStack_1031_, v___y_1025_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1032_);
lean_ctor_set(v___x_1038_, 1, v_a_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Lean_Elab_abortTermExceptionId;
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_1059_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_1064_ = l_Lean_MessageData_ofExpr(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_1066_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_1072_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_ty_x3f_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_fileName_1094_; lean_object* v_fileMap_1095_; lean_object* v_options_1096_; lean_object* v_currRecDepth_1097_; lean_object* v_maxRecDepth_1098_; lean_object* v_ref_1099_; lean_object* v_currNamespace_1100_; lean_object* v_openDecls_1101_; lean_object* v_initHeartbeats_1102_; lean_object* v_maxHeartbeats_1103_; lean_object* v_quotContext_1104_; lean_object* v_currMacroScope_1105_; uint8_t v_diag_1106_; lean_object* v_cancelTk_x3f_1107_; uint8_t v_suppressElabErrors_1108_; lean_object* v_inheritedTraceOptions_1109_; uint8_t v___x_1110_; lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_ty_x3f_1088_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_1089_ = 1;
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_box(v___x_1089_);
v___x_1092_ = lean_box(v___x_1089_);
lean_inc(v_stx_1080_);
v___x_1093_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1093_, 0, v_stx_1080_);
lean_closure_set(v___x_1093_, 1, v_ty_x3f_1088_);
lean_closure_set(v___x_1093_, 2, v___x_1091_);
lean_closure_set(v___x_1093_, 3, v___x_1092_);
lean_closure_set(v___x_1093_, 4, v___x_1090_);
v_fileName_1094_ = lean_ctor_get(v_a_1085_, 0);
v_fileMap_1095_ = lean_ctor_get(v_a_1085_, 1);
v_options_1096_ = lean_ctor_get(v_a_1085_, 2);
v_currRecDepth_1097_ = lean_ctor_get(v_a_1085_, 3);
v_maxRecDepth_1098_ = lean_ctor_get(v_a_1085_, 4);
v_ref_1099_ = lean_ctor_get(v_a_1085_, 5);
v_currNamespace_1100_ = lean_ctor_get(v_a_1085_, 6);
v_openDecls_1101_ = lean_ctor_get(v_a_1085_, 7);
v_initHeartbeats_1102_ = lean_ctor_get(v_a_1085_, 8);
v_maxHeartbeats_1103_ = lean_ctor_get(v_a_1085_, 9);
v_quotContext_1104_ = lean_ctor_get(v_a_1085_, 10);
v_currMacroScope_1105_ = lean_ctor_get(v_a_1085_, 11);
v_diag_1106_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*14);
v_cancelTk_x3f_1107_ = lean_ctor_get(v_a_1085_, 12);
v_suppressElabErrors_1108_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1109_ = lean_ctor_get(v_a_1085_, 13);
v___x_1110_ = 1;
v_ref_1111_ = l_Lean_replaceRef(v_stx_1080_, v_ref_1099_);
lean_dec(v_stx_1080_);
lean_inc_ref(v_inheritedTraceOptions_1109_);
lean_inc(v_cancelTk_x3f_1107_);
lean_inc(v_currMacroScope_1105_);
lean_inc(v_quotContext_1104_);
lean_inc(v_maxHeartbeats_1103_);
lean_inc(v_initHeartbeats_1102_);
lean_inc(v_openDecls_1101_);
lean_inc(v_currNamespace_1100_);
lean_inc(v_maxRecDepth_1098_);
lean_inc(v_currRecDepth_1097_);
lean_inc_ref(v_options_1096_);
lean_inc_ref(v_fileMap_1095_);
lean_inc_ref(v_fileName_1094_);
v___x_1112_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1112_, 0, v_fileName_1094_);
lean_ctor_set(v___x_1112_, 1, v_fileMap_1095_);
lean_ctor_set(v___x_1112_, 2, v_options_1096_);
lean_ctor_set(v___x_1112_, 3, v_currRecDepth_1097_);
lean_ctor_set(v___x_1112_, 4, v_maxRecDepth_1098_);
lean_ctor_set(v___x_1112_, 5, v_ref_1111_);
lean_ctor_set(v___x_1112_, 6, v_currNamespace_1100_);
lean_ctor_set(v___x_1112_, 7, v_openDecls_1101_);
lean_ctor_set(v___x_1112_, 8, v_initHeartbeats_1102_);
lean_ctor_set(v___x_1112_, 9, v_maxHeartbeats_1103_);
lean_ctor_set(v___x_1112_, 10, v_quotContext_1104_);
lean_ctor_set(v___x_1112_, 11, v_currMacroScope_1105_);
lean_ctor_set(v___x_1112_, 12, v_cancelTk_x3f_1107_);
lean_ctor_set(v___x_1112_, 13, v_inheritedTraceOptions_1109_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*14, v_diag_1106_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*14 + 1, v_suppressElabErrors_1108_);
v___x_1113_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1093_, v___x_1110_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v___x_1112_, v_a_1086_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v_a_1116_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; uint8_t v___x_1211_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_1114_, v_a_1084_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1115_);
v___x_1211_ = l_Lean_Expr_hasSorry(v_a_1116_);
if (v___x_1211_ == 0)
{
v___y_1156_ = v_a_1081_;
v___y_1157_ = v_a_1082_;
v___y_1158_ = v_a_1083_;
v___y_1159_ = v_a_1084_;
v___y_1160_ = v___x_1112_;
v___y_1161_ = v_a_1086_;
goto v___jp_1155_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Lean_Expr_hasSyntheticSorry(v_a_1116_);
if (v___x_1212_ == 0)
{
v___y_1193_ = v_a_1081_;
v___y_1194_ = v_a_1082_;
v___y_1195_ = v_a_1083_;
v___y_1196_ = v_a_1084_;
v___y_1197_ = v___x_1112_;
v___y_1198_ = v_a_1086_;
goto v___jp_1192_;
}
else
{
lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1116_);
lean_dec_ref_known(v___x_1112_, 14);
v___x_1213_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
v___jp_1117_:
{
if (v___y_1127_ == 0)
{
if (lean_obj_tag(v___y_1118_) == 0)
{
lean_dec_ref_known(v___y_1118_, 2);
lean_dec_ref(v___y_1120_);
lean_dec(v_a_1116_);
return v___y_1125_;
}
else
{
lean_object* v_id_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1141_; 
v_id_1128_ = lean_ctor_get(v___y_1118_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___y_1118_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___y_1118_, 1);
lean_dec(v_unused_1142_);
v___x_1130_ = v___y_1118_;
v_isShared_1131_ = v_isSharedCheck_1141_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_id_1128_);
lean_dec(v___y_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1141_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1122_, v_id_1128_);
lean_dec(v_id_1128_);
if (v___x_1132_ == 0)
{
lean_del_object(v___x_1130_);
lean_dec_ref(v___y_1120_);
lean_dec(v_a_1116_);
return v___y_1125_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec_ref(v___y_1125_);
v___x_1133_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6);
v___x_1134_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_1135_ = l_Lean_indentExpr(v_a_1116_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 7);
lean_ctor_set(v___x_1130_, 1, v___x_1135_);
lean_ctor_set(v___x_1130_, 0, v___x_1134_);
v___x_1137_ = v___x_1130_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1133_);
v___x_1139_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1138_, v___y_1121_, v___y_1123_, v___y_1126_, v___y_1124_, v___y_1120_, v___y_1119_);
lean_dec_ref(v___y_1120_);
return v___x_1139_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1116_);
return v___y_1125_;
}
}
v___jp_1143_:
{
lean_object* v___x_1150_; 
lean_inc(v_a_1116_);
v___x_1150_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_1116_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_dec_ref(v___y_1148_);
lean_dec(v_a_1116_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
v___x_1152_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1153_ = l_Lean_Exception_isInterrupt(v_a_1151_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
lean_inc(v_a_1151_);
v___x_1154_ = l_Lean_Exception_isRuntime(v_a_1151_);
v___y_1118_ = v_a_1151_;
v___y_1119_ = v___y_1149_;
v___y_1120_ = v___y_1148_;
v___y_1121_ = v___y_1144_;
v___y_1122_ = v___x_1152_;
v___y_1123_ = v___y_1145_;
v___y_1124_ = v___y_1147_;
v___y_1125_ = v___x_1150_;
v___y_1126_ = v___y_1146_;
v___y_1127_ = v___x_1154_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v_a_1151_;
v___y_1119_ = v___y_1149_;
v___y_1120_ = v___y_1148_;
v___y_1121_ = v___y_1144_;
v___y_1122_ = v___x_1152_;
v___y_1123_ = v___y_1145_;
v___y_1124_ = v___y_1147_;
v___y_1125_ = v___x_1150_;
v___y_1126_ = v___y_1146_;
v___y_1127_ = v___x_1153_;
goto v___jp_1117_;
}
}
}
v___jp_1155_:
{
lean_object* v___x_1162_; 
lean_inc(v_a_1116_);
v___x_1162_ = l_Lean_Meta_getMVars(v_a_1116_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1163_, v___x_1090_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v_a_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; uint8_t v___x_1166_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_unbox(v_a_1165_);
lean_dec(v_a_1165_);
if (v___x_1166_ == 0)
{
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1157_;
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1159_;
v___y_1148_ = v___y_1160_;
v___y_1149_ = v___y_1161_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1167_; lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v___y_1160_);
lean_dec(v_a_1116_);
v___x_1167_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v___y_1160_);
lean_dec(v_a_1116_);
v_a_1176_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1164_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___y_1160_);
lean_dec(v_a_1116_);
v_a_1184_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1162_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1162_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
v___jp_1192_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v___x_1199_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_1200_ = l_Lean_indentExpr(v_a_1116_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1201_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec_ref(v___y_1197_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref_known(v___x_1112_, 14);
v_a_1222_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1113_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1113_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_stx_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(lean_object* v_config_1308_, lean_object* v_item_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_item_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1328_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1309_, v___x_1327_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1328_) == 0)
{
uint8_t v___x_1329_; 
lean_dec_ref_known(v___x_1328_, 1);
v___x_1329_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1309_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1330_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1309_);
lean_inc_ref(v_item_1309_);
v___x_1331_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1309_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_1333_ = lean_string_dec_lt(v___x_1330_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_1335_ = lean_string_dec_lt(v___x_1330_, v___x_1334_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_string_dec_eq(v___x_1330_, v___x_1334_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_1338_ = lean_string_dec_eq(v___x_1330_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_1340_ = lean_string_dec_eq(v___x_1330_, v___x_1339_);
lean_dec_ref(v___x_1330_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_1342_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1341_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1342_) == 0)
{
uint8_t v___x_1343_; 
lean_dec_ref_known(v___x_1342_, 1);
v___x_1343_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1331_);
v___x_1344_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1370_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1370_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1370_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v_proofs_1349_; uint8_t v_types_1350_; uint8_t v_implicits_1351_; uint8_t v_descend_1352_; uint8_t v_underBinder_1353_; uint8_t v_merge_1354_; uint8_t v_useContext_1355_; uint8_t v_onlyGivenNames_1356_; uint8_t v_preserveBinderNames_1357_; uint8_t v_lift_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
v_proofs_1349_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1350_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1351_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1352_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1353_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_merge_1354_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1355_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1356_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1357_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1358_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1360_ = v_config_1308_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v_config_1308_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 0, v_proofs_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 1, v_types_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 2, v_implicits_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 3, v_descend_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 4, v_underBinder_1353_);
v___x_1363_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
uint8_t v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
lean_ctor_set_uint8(v___x_1363_, 5, v___x_1364_);
lean_ctor_set_uint8(v___x_1363_, 6, v_merge_1354_);
lean_ctor_set_uint8(v___x_1363_, 7, v_useContext_1355_);
lean_ctor_set_uint8(v___x_1363_, 8, v_onlyGivenNames_1356_);
lean_ctor_set_uint8(v___x_1363_, 9, v_preserveBinderNames_1357_);
lean_ctor_set_uint8(v___x_1363_, 10, v_lift_1358_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1363_);
v___x_1366_ = v___x_1347_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1363_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_config_1308_);
v_a_1371_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1344_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1344_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1379_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1342_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1342_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v___x_1330_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_1388_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1387_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1388_) == 0)
{
uint8_t v___x_1389_; 
lean_dec_ref_known(v___x_1388_, 1);
v___x_1389_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1390_; 
lean_dec_ref(v___x_1331_);
v___x_1390_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1416_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1416_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1416_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v_proofs_1395_; uint8_t v_types_1396_; uint8_t v_implicits_1397_; uint8_t v_descend_1398_; uint8_t v_underBinder_1399_; uint8_t v_usedOnly_1400_; uint8_t v_merge_1401_; uint8_t v_onlyGivenNames_1402_; uint8_t v_preserveBinderNames_1403_; uint8_t v_lift_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1415_; 
v_proofs_1395_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1396_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1397_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1398_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1399_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1400_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1401_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_onlyGivenNames_1402_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1403_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1404_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1406_ = v_config_1308_;
v_isShared_1407_ = v_isSharedCheck_1415_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_config_1308_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1415_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 0, v_proofs_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 1, v_types_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 2, v_implicits_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 3, v_descend_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 4, v_underBinder_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 5, v_usedOnly_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, 6, v_merge_1401_);
v___x_1409_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
uint8_t v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
lean_ctor_set_uint8(v___x_1409_, 7, v___x_1410_);
lean_ctor_set_uint8(v___x_1409_, 8, v_onlyGivenNames_1402_);
lean_ctor_set_uint8(v___x_1409_, 9, v_preserveBinderNames_1403_);
lean_ctor_set_uint8(v___x_1409_, 10, v_lift_1404_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1409_);
v___x_1412_ = v___x_1393_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1409_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_config_1308_);
v_a_1417_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1390_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1390_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1425_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1388_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1388_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v___x_1330_);
v___x_1433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_1434_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1433_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1434_) == 0)
{
uint8_t v___x_1435_; 
lean_dec_ref_known(v___x_1434_, 1);
v___x_1435_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1435_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1436_; 
lean_dec_ref(v___x_1331_);
v___x_1436_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1462_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1462_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1462_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v_proofs_1441_; uint8_t v_types_1442_; uint8_t v_implicits_1443_; uint8_t v_descend_1444_; uint8_t v_usedOnly_1445_; uint8_t v_merge_1446_; uint8_t v_useContext_1447_; uint8_t v_onlyGivenNames_1448_; uint8_t v_preserveBinderNames_1449_; uint8_t v_lift_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1461_; 
v_proofs_1441_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1442_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1443_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1444_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_usedOnly_1445_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1446_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1447_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1448_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1449_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1450_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1452_ = v_config_1308_;
v_isShared_1453_ = v_isSharedCheck_1461_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_config_1308_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1461_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, 0, v_proofs_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, 1, v_types_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, 2, v_implicits_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, 3, v_descend_1444_);
v___x_1455_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
uint8_t v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_unbox(v_a_1437_);
lean_dec(v_a_1437_);
lean_ctor_set_uint8(v___x_1455_, 4, v___x_1456_);
lean_ctor_set_uint8(v___x_1455_, 5, v_usedOnly_1445_);
lean_ctor_set_uint8(v___x_1455_, 6, v_merge_1446_);
lean_ctor_set_uint8(v___x_1455_, 7, v_useContext_1447_);
lean_ctor_set_uint8(v___x_1455_, 8, v_onlyGivenNames_1448_);
lean_ctor_set_uint8(v___x_1455_, 9, v_preserveBinderNames_1449_);
lean_ctor_set_uint8(v___x_1455_, 10, v_lift_1450_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1455_);
v___x_1458_ = v___x_1439_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_config_1308_);
v_a_1463_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1436_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1436_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1471_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1434_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1434_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_string_dec_eq(v___x_1330_, v___x_1332_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_1481_ = lean_string_dec_eq(v___x_1330_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_1483_ = lean_string_dec_eq(v___x_1330_, v___x_1482_);
lean_dec_ref(v___x_1330_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_1485_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1484_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1485_) == 0)
{
uint8_t v___x_1486_; 
lean_dec_ref_known(v___x_1485_, 1);
v___x_1486_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1487_; 
lean_dec_ref(v___x_1331_);
v___x_1487_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1513_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1513_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1513_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
uint8_t v_proofs_1492_; uint8_t v_implicits_1493_; uint8_t v_descend_1494_; uint8_t v_underBinder_1495_; uint8_t v_usedOnly_1496_; uint8_t v_merge_1497_; uint8_t v_useContext_1498_; uint8_t v_onlyGivenNames_1499_; uint8_t v_preserveBinderNames_1500_; uint8_t v_lift_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
v_proofs_1492_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_implicits_1493_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1494_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1495_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1496_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1497_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1498_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1499_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1500_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1501_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1503_ = v_config_1308_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_config_1308_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1511_, 0, v_proofs_1492_);
v___x_1506_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
uint8_t v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_unbox(v_a_1488_);
lean_dec(v_a_1488_);
lean_ctor_set_uint8(v___x_1506_, 1, v___x_1507_);
lean_ctor_set_uint8(v___x_1506_, 2, v_implicits_1493_);
lean_ctor_set_uint8(v___x_1506_, 3, v_descend_1494_);
lean_ctor_set_uint8(v___x_1506_, 4, v_underBinder_1495_);
lean_ctor_set_uint8(v___x_1506_, 5, v_usedOnly_1496_);
lean_ctor_set_uint8(v___x_1506_, 6, v_merge_1497_);
lean_ctor_set_uint8(v___x_1506_, 7, v_useContext_1498_);
lean_ctor_set_uint8(v___x_1506_, 8, v_onlyGivenNames_1499_);
lean_ctor_set_uint8(v___x_1506_, 9, v_preserveBinderNames_1500_);
lean_ctor_set_uint8(v___x_1506_, 10, v_lift_1501_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1506_);
v___x_1509_ = v___x_1490_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1506_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_config_1308_);
v_a_1514_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1487_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1487_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1522_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1485_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1485_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v___x_1330_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_1531_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1530_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1531_) == 0)
{
uint8_t v___x_1532_; 
lean_dec_ref_known(v___x_1531_, 1);
v___x_1532_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1532_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1533_; 
lean_dec_ref(v___x_1331_);
v___x_1533_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1559_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v_types_1538_; uint8_t v_implicits_1539_; uint8_t v_descend_1540_; uint8_t v_underBinder_1541_; uint8_t v_usedOnly_1542_; uint8_t v_merge_1543_; uint8_t v_useContext_1544_; uint8_t v_onlyGivenNames_1545_; uint8_t v_preserveBinderNames_1546_; uint8_t v_lift_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1558_; 
v_types_1538_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1539_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1540_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1541_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1542_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1543_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1544_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1545_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1546_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1547_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1549_ = v_config_1308_;
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v_config_1308_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 0, 11);
v___x_1552_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
uint8_t v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
lean_ctor_set_uint8(v___x_1552_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1552_, 1, v_types_1538_);
lean_ctor_set_uint8(v___x_1552_, 2, v_implicits_1539_);
lean_ctor_set_uint8(v___x_1552_, 3, v_descend_1540_);
lean_ctor_set_uint8(v___x_1552_, 4, v_underBinder_1541_);
lean_ctor_set_uint8(v___x_1552_, 5, v_usedOnly_1542_);
lean_ctor_set_uint8(v___x_1552_, 6, v_merge_1543_);
lean_ctor_set_uint8(v___x_1552_, 7, v_useContext_1544_);
lean_ctor_set_uint8(v___x_1552_, 8, v_onlyGivenNames_1545_);
lean_ctor_set_uint8(v___x_1552_, 9, v_preserveBinderNames_1546_);
lean_ctor_set_uint8(v___x_1552_, 10, v_lift_1547_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1552_);
v___x_1555_ = v___x_1536_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1552_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_config_1308_);
v_a_1560_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1533_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1533_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1568_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1531_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1531_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref(v___x_1330_);
v___x_1576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_1577_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1576_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1577_) == 0)
{
uint8_t v___x_1578_; 
lean_dec_ref_known(v___x_1577_, 1);
v___x_1578_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1579_; 
lean_dec_ref(v___x_1331_);
v___x_1579_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1605_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1605_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1605_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v_proofs_1584_; uint8_t v_types_1585_; uint8_t v_implicits_1586_; uint8_t v_descend_1587_; uint8_t v_underBinder_1588_; uint8_t v_usedOnly_1589_; uint8_t v_merge_1590_; uint8_t v_useContext_1591_; uint8_t v_onlyGivenNames_1592_; uint8_t v_lift_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1604_; 
v_proofs_1584_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1585_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1586_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1587_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1588_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1589_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1590_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1591_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1592_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_lift_1593_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1595_ = v_config_1308_;
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_config_1308_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 0, v_proofs_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 1, v_types_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 2, v_implicits_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 3, v_descend_1587_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 4, v_underBinder_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 5, v_usedOnly_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 6, v_merge_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 7, v_useContext_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, 8, v_onlyGivenNames_1592_);
v___x_1598_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
uint8_t v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
lean_ctor_set_uint8(v___x_1598_, 9, v___x_1599_);
lean_ctor_set_uint8(v___x_1598_, 10, v_lift_1593_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1598_);
v___x_1601_ = v___x_1582_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1598_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_config_1308_);
v_a_1606_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1579_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1579_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1614_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1577_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1577_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
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
}
else
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_1623_ = lean_string_dec_lt(v___x_1330_, v___x_1622_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_string_dec_eq(v___x_1330_, v___x_1622_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_1626_ = lean_string_dec_eq(v___x_1330_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_1628_ = lean_string_dec_eq(v___x_1330_, v___x_1627_);
lean_dec_ref(v___x_1330_);
if (v___x_1628_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_1630_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1629_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1630_) == 0)
{
uint8_t v___x_1631_; 
lean_dec_ref_known(v___x_1630_, 1);
v___x_1631_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1631_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1632_; 
lean_dec_ref(v___x_1331_);
v___x_1632_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1658_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1658_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1658_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v_proofs_1637_; uint8_t v_types_1638_; uint8_t v_implicits_1639_; uint8_t v_descend_1640_; uint8_t v_underBinder_1641_; uint8_t v_usedOnly_1642_; uint8_t v_merge_1643_; uint8_t v_useContext_1644_; uint8_t v_preserveBinderNames_1645_; uint8_t v_lift_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1657_; 
v_proofs_1637_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1638_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1639_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1640_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1641_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1642_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1643_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1644_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_preserveBinderNames_1645_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1646_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1648_ = v_config_1308_;
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_config_1308_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 0, v_proofs_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 1, v_types_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 2, v_implicits_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 3, v_descend_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 4, v_underBinder_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 5, v_usedOnly_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 6, v_merge_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, 7, v_useContext_1644_);
v___x_1651_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
uint8_t v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unbox(v_a_1633_);
lean_dec(v_a_1633_);
lean_ctor_set_uint8(v___x_1651_, 8, v___x_1652_);
lean_ctor_set_uint8(v___x_1651_, 9, v_preserveBinderNames_1645_);
lean_ctor_set_uint8(v___x_1651_, 10, v_lift_1646_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1651_);
v___x_1654_ = v___x_1635_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1651_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_config_1308_);
v_a_1659_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1632_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1632_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1667_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1630_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1630_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec_ref(v___x_1330_);
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_1676_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1675_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1676_) == 0)
{
uint8_t v___x_1677_; 
lean_dec_ref_known(v___x_1676_, 1);
v___x_1677_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1678_; 
lean_dec_ref(v___x_1331_);
v___x_1678_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1704_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1704_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1704_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
uint8_t v_proofs_1683_; uint8_t v_types_1684_; uint8_t v_implicits_1685_; uint8_t v_descend_1686_; uint8_t v_underBinder_1687_; uint8_t v_usedOnly_1688_; uint8_t v_useContext_1689_; uint8_t v_onlyGivenNames_1690_; uint8_t v_preserveBinderNames_1691_; uint8_t v_lift_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1703_; 
v_proofs_1683_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1684_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1685_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1686_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1687_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1688_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_useContext_1689_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1690_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1691_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1692_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1694_ = v_config_1308_;
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_config_1308_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 0, v_proofs_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 1, v_types_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 2, v_implicits_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 3, v_descend_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 4, v_underBinder_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, 5, v_usedOnly_1688_);
v___x_1697_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
uint8_t v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
lean_ctor_set_uint8(v___x_1697_, 6, v___x_1698_);
lean_ctor_set_uint8(v___x_1697_, 7, v_useContext_1689_);
lean_ctor_set_uint8(v___x_1697_, 8, v_onlyGivenNames_1690_);
lean_ctor_set_uint8(v___x_1697_, 9, v_preserveBinderNames_1691_);
lean_ctor_set_uint8(v___x_1697_, 10, v_lift_1692_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1697_);
v___x_1700_ = v___x_1681_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1697_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_config_1308_);
v_a_1705_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1678_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1678_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1713_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1676_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1676_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec_ref(v___x_1330_);
v___x_1721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_1722_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1721_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1722_) == 0)
{
uint8_t v___x_1723_; 
lean_dec_ref_known(v___x_1722_, 1);
v___x_1723_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1723_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1724_; 
lean_dec_ref(v___x_1331_);
v___x_1724_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1750_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1750_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1750_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
uint8_t v_proofs_1729_; uint8_t v_types_1730_; uint8_t v_implicits_1731_; uint8_t v_descend_1732_; uint8_t v_underBinder_1733_; uint8_t v_usedOnly_1734_; uint8_t v_merge_1735_; uint8_t v_useContext_1736_; uint8_t v_onlyGivenNames_1737_; uint8_t v_preserveBinderNames_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1749_; 
v_proofs_1729_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1730_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1731_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_descend_1732_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1733_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1734_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1735_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1736_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1737_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1738_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1740_ = v_config_1308_;
v_isShared_1741_ = v_isSharedCheck_1749_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v_config_1308_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1749_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 0, v_proofs_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 1, v_types_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 2, v_implicits_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 3, v_descend_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 4, v_underBinder_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 5, v_usedOnly_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 6, v_merge_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 7, v_useContext_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 8, v_onlyGivenNames_1737_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, 9, v_preserveBinderNames_1738_);
v___x_1743_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
uint8_t v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_unbox(v_a_1725_);
lean_dec(v_a_1725_);
lean_ctor_set_uint8(v___x_1743_, 10, v___x_1744_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1743_);
v___x_1746_ = v___x_1727_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1743_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v_config_1308_);
v_a_1751_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1724_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1724_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1759_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1722_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1722_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_1768_ = lean_string_dec_eq(v___x_1330_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_1770_ = lean_string_dec_eq(v___x_1330_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_1772_ = lean_string_dec_eq(v___x_1330_, v___x_1771_);
lean_dec_ref(v___x_1330_);
if (v___x_1772_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_1774_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1773_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1774_) == 0)
{
uint8_t v___x_1775_; 
lean_dec_ref_known(v___x_1774_, 1);
v___x_1775_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1775_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1776_; 
lean_dec_ref(v___x_1331_);
v___x_1776_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1802_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1802_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1802_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint8_t v_proofs_1781_; uint8_t v_types_1782_; uint8_t v_descend_1783_; uint8_t v_underBinder_1784_; uint8_t v_usedOnly_1785_; uint8_t v_merge_1786_; uint8_t v_useContext_1787_; uint8_t v_onlyGivenNames_1788_; uint8_t v_preserveBinderNames_1789_; uint8_t v_lift_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1801_; 
v_proofs_1781_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1782_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_descend_1783_ = lean_ctor_get_uint8(v_config_1308_, 3);
v_underBinder_1784_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1785_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1786_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1787_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1788_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1789_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1790_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1792_ = v_config_1308_;
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_config_1308_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, 0, v_proofs_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, 1, v_types_1782_);
v___x_1795_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
uint8_t v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
lean_ctor_set_uint8(v___x_1795_, 2, v___x_1796_);
lean_ctor_set_uint8(v___x_1795_, 3, v_descend_1783_);
lean_ctor_set_uint8(v___x_1795_, 4, v_underBinder_1784_);
lean_ctor_set_uint8(v___x_1795_, 5, v_usedOnly_1785_);
lean_ctor_set_uint8(v___x_1795_, 6, v_merge_1786_);
lean_ctor_set_uint8(v___x_1795_, 7, v_useContext_1787_);
lean_ctor_set_uint8(v___x_1795_, 8, v_onlyGivenNames_1788_);
lean_ctor_set_uint8(v___x_1795_, 9, v_preserveBinderNames_1789_);
lean_ctor_set_uint8(v___x_1795_, 10, v_lift_1790_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1795_);
v___x_1798_ = v___x_1779_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1795_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_config_1308_);
v_a_1803_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1776_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1776_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1811_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1774_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1774_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v___x_1330_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_1820_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1309_, v___x_1819_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1820_) == 0)
{
uint8_t v___x_1821_; 
lean_dec_ref_known(v___x_1820_, 1);
v___x_1821_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1821_ == 0)
{
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1331_);
v___x_1822_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1848_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1848_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1848_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
uint8_t v_proofs_1827_; uint8_t v_types_1828_; uint8_t v_implicits_1829_; uint8_t v_underBinder_1830_; uint8_t v_usedOnly_1831_; uint8_t v_merge_1832_; uint8_t v_useContext_1833_; uint8_t v_onlyGivenNames_1834_; uint8_t v_preserveBinderNames_1835_; uint8_t v_lift_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1847_; 
v_proofs_1827_ = lean_ctor_get_uint8(v_config_1308_, 0);
v_types_1828_ = lean_ctor_get_uint8(v_config_1308_, 1);
v_implicits_1829_ = lean_ctor_get_uint8(v_config_1308_, 2);
v_underBinder_1830_ = lean_ctor_get_uint8(v_config_1308_, 4);
v_usedOnly_1831_ = lean_ctor_get_uint8(v_config_1308_, 5);
v_merge_1832_ = lean_ctor_get_uint8(v_config_1308_, 6);
v_useContext_1833_ = lean_ctor_get_uint8(v_config_1308_, 7);
v_onlyGivenNames_1834_ = lean_ctor_get_uint8(v_config_1308_, 8);
v_preserveBinderNames_1835_ = lean_ctor_get_uint8(v_config_1308_, 9);
v_lift_1836_ = lean_ctor_get_uint8(v_config_1308_, 10);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_config_1308_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1838_ = v_config_1308_;
v_isShared_1839_ = v_isSharedCheck_1847_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v_config_1308_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1847_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, 0, v_proofs_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, 1, v_types_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, 2, v_implicits_1829_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
uint8_t v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_unbox(v_a_1823_);
lean_dec(v_a_1823_);
lean_ctor_set_uint8(v___x_1841_, 3, v___x_1842_);
lean_ctor_set_uint8(v___x_1841_, 4, v_underBinder_1830_);
lean_ctor_set_uint8(v___x_1841_, 5, v_usedOnly_1831_);
lean_ctor_set_uint8(v___x_1841_, 6, v_merge_1832_);
lean_ctor_set_uint8(v___x_1841_, 7, v_useContext_1833_);
lean_ctor_set_uint8(v___x_1841_, 8, v_onlyGivenNames_1834_);
lean_ctor_set_uint8(v___x_1841_, 9, v_preserveBinderNames_1835_);
lean_ctor_set_uint8(v___x_1841_, 10, v_lift_1836_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1841_);
v___x_1844_ = v___x_1825_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1841_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v_config_1308_);
v_a_1849_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1822_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1822_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1857_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1820_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1820_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
uint8_t v___x_1865_; 
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_config_1308_);
v___x_1865_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1331_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v_item_1309_);
v_item_1318_ = v___x_1331_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
else
{
lean_object* v_value_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v___x_1331_);
v_value_1866_ = lean_ctor_get(v_item_1309_, 2);
lean_inc(v_value_1866_);
lean_dec_ref(v_item_1309_);
v___x_1867_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_value_1866_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1867_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_1308_);
v_item_1318_ = v_item_1309_;
v___y_1319_ = v___y_1310_;
v___y_1320_ = v___y_1311_;
v___y_1321_ = v___y_1312_;
v___y_1322_ = v___y_1313_;
v___y_1323_ = v___y_1314_;
v___y_1324_ = v___y_1315_;
goto v___jp_1317_;
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_item_1309_);
lean_dec_ref(v_config_1308_);
v_a_1868_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1328_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1328_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
v___jp_1317_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_1326_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1318_, v___x_1325_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1876_, lean_object* v_item_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(v_config_1876_, v_item_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1888_, v___y_1892_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(v_e_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1934_, v_msg_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1944_, lean_object* v_macroStack_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1944_, v_macroStack_1945_, v___y_1950_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1954_, lean_object* v_macroStack_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1954_, v_macroStack_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1963_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = lean_box(0);
v___x_1965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1966_ = l_Lean_mkConst(v___x_1965_, v___x_1964_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(lean_object* v_cfg_1969_, lean_object* v_cfgItem_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1);
v___x_1979_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1969_, v_cfgItem_1970_, v___x_1978_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_1980_, lean_object* v_cfgItem_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(v_cfg_1980_, v_cfgItem_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v_cfgItem_1981_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_cfg_1991_, lean_object* v_init_1992_, uint8_t v_logExceptions_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_onErr_1998_; lean_object* v_eval_1999_; 
v_onErr_1998_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v_eval_1999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_1993_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1999_, v_init_1992_, v_cfg_1991_, v_onErr_1998_, v_logExceptions_1993_, v_a_1995_, v_a_1996_);
return v___x_2000_;
}
else
{
uint8_t v_recover_2001_; lean_object* v___x_2002_; 
v_recover_2001_ = lean_ctor_get_uint8(v_a_1994_, sizeof(void*)*1);
v___x_2002_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1999_, v_init_1992_, v_cfg_1991_, v_onErr_1998_, v_recover_2001_, v_a_1995_, v_a_1996_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_cfg_2003_, lean_object* v_init_2004_, lean_object* v_logExceptions_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
uint8_t v_logExceptions_boxed_2010_; lean_object* v_res_2011_; 
v_logExceptions_boxed_2010_ = lean_unbox(v_logExceptions_2005_);
v_res_2011_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_2003_, v_init_2004_, v_logExceptions_boxed_2010_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_cfg_2012_, lean_object* v_init_2013_, uint8_t v_logExceptions_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_2012_, v_init_2013_, v_logExceptions_2014_, v_a_2015_, v_a_2021_, v_a_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_cfg_2025_, lean_object* v_init_2026_, lean_object* v_logExceptions_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v_logExceptions_boxed_2037_; lean_object* v_res_2038_; 
v_logExceptions_boxed_2037_ = lean_unbox(v_logExceptions_2027_);
v_res_2038_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_cfg_2025_, v_init_2026_, v_logExceptions_boxed_2037_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2038_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_ref_2075_; lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2085_; 
v_ref_2075_ = lean_ctor_get(v___y_2072_, 5);
v___x_2076_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
lean_inc(v_ref_2075_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_ref_2075_);
lean_ctor_set(v___x_2081_, 1, v_a_2077_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v_msg_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2092_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_2095_ = l_Lean_stringToMessageData(v___x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_2107_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2106_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v_x_2108_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_2119_, lean_object* v___x_2120_, lean_object* v_a_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2123_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_2132_, v_h_2119_, v___x_2120_, v_a_2121_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v_fst_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2162_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_fst_2135_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_fst_2135_);
v_snd_2136_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_snd_2136_);
lean_dec(v_a_2134_);
v_fst_2137_ = lean_ctor_get(v_fst_2135_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_fst_2135_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_fst_2135_, 1);
lean_dec(v_unused_2163_);
v___x_2139_ = v_fst_2135_;
v_isShared_2140_ = v_isSharedCheck_2162_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_fst_2137_);
lean_dec(v_fst_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2162_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(0);
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 1);
lean_ctor_set(v___x_2139_, 1, v___x_2141_);
lean_ctor_set(v___x_2139_, 0, v_snd_2136_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_snd_2136_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2143_, v___y_2123_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2144_, 0);
lean_dec(v_unused_2152_);
v___x_2146_ = v___x_2144_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v___x_2144_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v_fst_2137_);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_fst_2137_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_fst_2137_);
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2133_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2133_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_a_2121_);
lean_dec(v___x_2120_);
lean_dec(v_h_2119_);
v_a_2172_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2131_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2131_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_2180_, lean_object* v___x_2181_, lean_object* v_a_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_2180_, v___x_2181_, v_a_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_2193_, lean_object* v_a_2194_, lean_object* v_ids_2195_, lean_object* v_h_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___f_2206_; lean_object* v___x_2207_; 
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2206_, 0, v_h_2196_);
lean_closure_set(v___f_2206_, 1, v___x_2193_);
lean_closure_set(v___f_2206_, 2, v_a_2194_);
v___x_2207_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2206_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2195_, v_a_2208_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2209_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_ids_2195_);
v_a_2210_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2207_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2207_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_2218_, lean_object* v_a_2219_, lean_object* v_ids_2220_, lean_object* v_h_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_2218_, v_a_2219_, v_ids_2220_, v_h_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_2232_, lean_object* v_a_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2235_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v___x_2245_ = l_Lean_MVarId_extractLets(v_a_2244_, v___x_2232_, v_a_2233_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v_fst_2247_; lean_object* v_snd_2248_; lean_object* v_fst_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2274_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v_fst_2247_ = lean_ctor_get(v_a_2246_, 0);
lean_inc(v_fst_2247_);
v_snd_2248_ = lean_ctor_get(v_a_2246_, 1);
lean_inc(v_snd_2248_);
lean_dec(v_a_2246_);
v_fst_2249_ = lean_ctor_get(v_fst_2247_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_fst_2247_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v_fst_2247_, 1);
lean_dec(v_unused_2275_);
v___x_2251_ = v_fst_2247_;
v_isShared_2252_ = v_isSharedCheck_2274_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_fst_2249_);
lean_dec(v_fst_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2274_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = lean_box(0);
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 1);
lean_ctor_set(v___x_2251_, 1, v___x_2253_);
lean_ctor_set(v___x_2251_, 0, v_snd_2248_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_snd_2248_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2255_, v___y_2235_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; 
v_unused_2264_ = lean_ctor_get(v___x_2256_, 0);
lean_dec(v_unused_2264_);
v___x_2258_ = v___x_2256_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v___x_2256_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_fst_2249_);
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_fst_2249_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_fst_2249_);
v_a_2265_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2256_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2256_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2245_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2245_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_a_2233_);
lean_dec(v___x_2232_);
v_a_2284_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2243_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2243_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_2292_, lean_object* v_a_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_2292_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_2304_, lean_object* v_ids_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2304_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2305_, v_a_2316_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2317_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_ids_2305_);
v_a_2318_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2315_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2315_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_2326_, lean_object* v_ids_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_2326_, v_ids_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_bs_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2341_ == 0)
{
return v_bs_2340_;
}
else
{
lean_object* v_v_2342_; lean_object* v___x_2343_; lean_object* v_bs_x27_2344_; lean_object* v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v_v_2342_ = lean_array_uget(v_bs_2340_, v_i_2339_);
v___x_2343_ = lean_unsigned_to_nat(0u);
v_bs_x27_2344_ = lean_array_uset(v_bs_2340_, v_i_2339_, v___x_2343_);
v___x_2345_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_2342_);
lean_dec(v_v_2342_);
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_add(v_i_2339_, v___x_2346_);
v___x_2348_ = lean_array_uset(v_bs_x27_2344_, v_i_2339_, v___x_2345_);
v_i_2339_ = v___x_2347_;
v_bs_2340_ = v___x_2348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_2350_, lean_object* v_i_2351_, lean_object* v_bs_2352_){
_start:
{
size_t v_sz_boxed_2353_; size_t v_i_boxed_2354_; lean_object* v_res_2355_; 
v_sz_boxed_2353_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_2353_, v_i_boxed_2354_, v_bs_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_2376_);
v___x_2403_ = l_Lean_Syntax_isOfKind(v_x_2376_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
lean_dec(v_x_2376_);
v___x_2404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2404_;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = l_Lean_Syntax_getArg(v_x_2376_, v___x_2405_);
v___x_2407_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2406_);
v___x_2408_ = l_Lean_Syntax_isOfKind(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec(v___x_2406_);
lean_dec(v_x_2376_);
v___x_2409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2409_;
}
else
{
lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_loc_x3f_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___f_2410_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_2411_ = lean_unsigned_to_nat(2u);
v___x_2412_ = l_Lean_Syntax_getArg(v_x_2376_, v___x_2411_);
v___x_2452_ = lean_unsigned_to_nat(3u);
v___x_2453_ = l_Lean_Syntax_getArg(v_x_2376_, v___x_2452_);
lean_dec(v_x_2376_);
v___x_2454_ = l_Lean_Syntax_isNone(v___x_2453_);
if (v___x_2454_ == 0)
{
uint8_t v___x_2455_; 
lean_inc(v___x_2453_);
v___x_2455_ = l_Lean_Syntax_matchesNull(v___x_2453_, v___x_2405_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_dec(v___x_2453_);
lean_dec(v___x_2412_);
lean_dec(v___x_2406_);
v___x_2456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; lean_object* v_loc_x3f_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2457_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2458_ = l_Lean_Syntax_getArg(v___x_2453_, v___x_2457_);
lean_dec(v___x_2453_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2458_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_dec(v_loc_x3f_2458_);
lean_dec(v___x_2412_);
lean_dec(v___x_2406_);
v___x_2461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_loc_x3f_2458_);
v_loc_x3f_2414_ = v___x_2462_;
v___y_2415_ = v_a_2377_;
v___y_2416_ = v_a_2378_;
v___y_2417_ = v_a_2379_;
v___y_2418_ = v_a_2380_;
v___y_2419_ = v_a_2381_;
v___y_2420_ = v_a_2382_;
v___y_2421_ = v_a_2383_;
v___y_2422_ = v_a_2384_;
goto v___jp_2413_;
}
}
}
else
{
lean_object* v___x_2463_; 
lean_dec(v___x_2453_);
v___x_2463_ = lean_box(0);
v_loc_x3f_2414_ = v___x_2463_;
v___y_2415_ = v_a_2377_;
v___y_2416_ = v_a_2378_;
v___y_2417_ = v_a_2379_;
v___y_2418_ = v_a_2380_;
v___y_2419_ = v_a_2381_;
v___y_2420_ = v_a_2382_;
v___y_2421_ = v_a_2383_;
v___y_2422_ = v_a_2384_;
goto v___jp_2413_;
}
v___jp_2413_:
{
uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = 0;
v___x_2424_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2424_, 0, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, 1, v___x_2408_);
lean_ctor_set_uint8(v___x_2424_, 2, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, 3, v___x_2408_);
lean_ctor_set_uint8(v___x_2424_, 4, v___x_2408_);
lean_ctor_set_uint8(v___x_2424_, 5, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, 6, v___x_2408_);
lean_ctor_set_uint8(v___x_2424_, 7, v___x_2408_);
lean_ctor_set_uint8(v___x_2424_, 8, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, 9, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, 10, v___x_2423_);
v___x_2425_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_2406_, v___x_2424_, v___x_2408_, v___y_2415_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v_ids_2427_; size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___f_2434_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc_n(v_a_2426_, 2);
lean_dec_ref_known(v___x_2425_, 1);
v_ids_2427_ = l_Lean_Syntax_getArgs(v___x_2412_);
lean_dec(v___x_2412_);
v_sz_2428_ = lean_array_size(v_ids_2427_);
v___x_2429_ = ((size_t)0ULL);
lean_inc_ref_n(v_ids_2427_, 2);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_2428_, v___x_2429_, v_ids_2427_);
v___x_2431_ = lean_array_to_list(v___x_2430_);
lean_inc(v___x_2431_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_2432_, 0, v___x_2431_);
lean_closure_set(v___f_2432_, 1, v_a_2426_);
lean_closure_set(v___f_2432_, 2, v_ids_2427_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2433_, 0, v___x_2431_);
lean_closure_set(v___f_2433_, 1, v_a_2426_);
v___f_2434_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_2434_, 0, v___f_2433_);
lean_closure_set(v___f_2434_, 1, v_ids_2427_);
if (lean_obj_tag(v_loc_x3f_2414_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_box(0);
v___y_2387_ = v___y_2415_;
v___y_2388_ = v___y_2420_;
v___y_2389_ = v___y_2422_;
v___y_2390_ = v___y_2416_;
v___y_2391_ = v___y_2419_;
v___y_2392_ = v___y_2417_;
v___y_2393_ = v___y_2418_;
v___y_2394_ = v___f_2410_;
v___y_2395_ = v___f_2432_;
v___y_2396_ = v___y_2421_;
v___y_2397_ = v___f_2434_;
v___y_2398_ = v___x_2435_;
goto v___jp_2386_;
}
else
{
lean_object* v_val_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_val_2436_ = lean_ctor_get(v_loc_x3f_2414_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_loc_x3f_2414_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v_loc_x3f_2414_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_val_2436_);
lean_dec(v_loc_x3f_2414_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_val_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
v___y_2387_ = v___y_2415_;
v___y_2388_ = v___y_2420_;
v___y_2389_ = v___y_2422_;
v___y_2390_ = v___y_2416_;
v___y_2391_ = v___y_2419_;
v___y_2392_ = v___y_2417_;
v___y_2393_ = v___y_2418_;
v___y_2394_ = v___f_2410_;
v___y_2395_ = v___f_2432_;
v___y_2396_ = v___y_2421_;
v___y_2397_ = v___f_2434_;
v___y_2398_ = v___x_2441_;
goto v___jp_2386_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_loc_x3f_2414_);
lean_dec(v___x_2412_);
v_a_2444_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2425_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2425_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
}
v___jp_2386_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = l_Lean_mkOptionalNode(v___y_2398_);
v___x_2400_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2399_);
lean_dec(v___x_2399_);
lean_inc_ref(v___y_2394_);
v___x_2401_ = l_Lean_Elab_Tactic_withLocation(v___x_2400_, v___y_2395_, v___y_2397_, v___y_2394_, v___y_2387_, v___y_2390_, v___y_2392_, v___y_2393_, v___y_2391_, v___y_2388_, v___y_2396_, v___y_2389_);
lean_dec(v___x_2400_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_2475_, lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_2476_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_2487_, lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_2487_, v_msg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2506_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2507_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_2508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_2509_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_2510_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object* v_ctor_2513_, lean_object* v_args_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_2542_ = lean_string_dec_eq(v_ctor_2513_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_array_get_size(v_args_2514_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_dec_eq(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v___x_2547_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_2548_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_2547_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
goto v___jp_2520_;
}
}
v___jp_2520_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2521_ = l_Lean_instInhabitedExpr;
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_borrowed(v___x_2521_, v_args_2514_, v___x_2522_);
lean_inc(v___x_2523_);
v___x_2524_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v___x_2523_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_a_2533_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2524_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2524_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_2557_, lean_object* v_args_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(v_ctor_2557_, v_args_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec_ref(v_args_2558_);
lean_dec_ref(v_ctor_2557_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___f_2577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0));
v___x_2578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2579_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2578_, v___f_2577_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2586_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
v___x_2589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2590_ = l_Lean_Expr_const___override(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0));
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig(void){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2598_ = l_Lean_MessageData_ofExpr(v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0);
v___x_2600_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_2603_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_ty_x3f_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_fileName_2619_; lean_object* v_fileMap_2620_; lean_object* v_options_2621_; lean_object* v_currRecDepth_2622_; lean_object* v_maxRecDepth_2623_; lean_object* v_ref_2624_; lean_object* v_currNamespace_2625_; lean_object* v_openDecls_2626_; lean_object* v_initHeartbeats_2627_; lean_object* v_maxHeartbeats_2628_; lean_object* v_quotContext_2629_; lean_object* v_currMacroScope_2630_; uint8_t v_diag_2631_; lean_object* v_cancelTk_x3f_2632_; uint8_t v_suppressElabErrors_2633_; lean_object* v_inheritedTraceOptions_2634_; uint8_t v___x_2635_; lean_object* v_ref_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_ty_x3f_2613_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2614_ = 1;
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_box(v___x_2614_);
v___x_2617_ = lean_box(v___x_2614_);
lean_inc(v_stx_2605_);
v___x_2618_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2618_, 0, v_stx_2605_);
lean_closure_set(v___x_2618_, 1, v_ty_x3f_2613_);
lean_closure_set(v___x_2618_, 2, v___x_2616_);
lean_closure_set(v___x_2618_, 3, v___x_2617_);
lean_closure_set(v___x_2618_, 4, v___x_2615_);
v_fileName_2619_ = lean_ctor_get(v_a_2610_, 0);
v_fileMap_2620_ = lean_ctor_get(v_a_2610_, 1);
v_options_2621_ = lean_ctor_get(v_a_2610_, 2);
v_currRecDepth_2622_ = lean_ctor_get(v_a_2610_, 3);
v_maxRecDepth_2623_ = lean_ctor_get(v_a_2610_, 4);
v_ref_2624_ = lean_ctor_get(v_a_2610_, 5);
v_currNamespace_2625_ = lean_ctor_get(v_a_2610_, 6);
v_openDecls_2626_ = lean_ctor_get(v_a_2610_, 7);
v_initHeartbeats_2627_ = lean_ctor_get(v_a_2610_, 8);
v_maxHeartbeats_2628_ = lean_ctor_get(v_a_2610_, 9);
v_quotContext_2629_ = lean_ctor_get(v_a_2610_, 10);
v_currMacroScope_2630_ = lean_ctor_get(v_a_2610_, 11);
v_diag_2631_ = lean_ctor_get_uint8(v_a_2610_, sizeof(void*)*14);
v_cancelTk_x3f_2632_ = lean_ctor_get(v_a_2610_, 12);
v_suppressElabErrors_2633_ = lean_ctor_get_uint8(v_a_2610_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2634_ = lean_ctor_get(v_a_2610_, 13);
v___x_2635_ = 1;
v_ref_2636_ = l_Lean_replaceRef(v_stx_2605_, v_ref_2624_);
lean_dec(v_stx_2605_);
lean_inc_ref(v_inheritedTraceOptions_2634_);
lean_inc(v_cancelTk_x3f_2632_);
lean_inc(v_currMacroScope_2630_);
lean_inc(v_quotContext_2629_);
lean_inc(v_maxHeartbeats_2628_);
lean_inc(v_initHeartbeats_2627_);
lean_inc(v_openDecls_2626_);
lean_inc(v_currNamespace_2625_);
lean_inc(v_maxRecDepth_2623_);
lean_inc(v_currRecDepth_2622_);
lean_inc_ref(v_options_2621_);
lean_inc_ref(v_fileMap_2620_);
lean_inc_ref(v_fileName_2619_);
v___x_2637_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2637_, 0, v_fileName_2619_);
lean_ctor_set(v___x_2637_, 1, v_fileMap_2620_);
lean_ctor_set(v___x_2637_, 2, v_options_2621_);
lean_ctor_set(v___x_2637_, 3, v_currRecDepth_2622_);
lean_ctor_set(v___x_2637_, 4, v_maxRecDepth_2623_);
lean_ctor_set(v___x_2637_, 5, v_ref_2636_);
lean_ctor_set(v___x_2637_, 6, v_currNamespace_2625_);
lean_ctor_set(v___x_2637_, 7, v_openDecls_2626_);
lean_ctor_set(v___x_2637_, 8, v_initHeartbeats_2627_);
lean_ctor_set(v___x_2637_, 9, v_maxHeartbeats_2628_);
lean_ctor_set(v___x_2637_, 10, v_quotContext_2629_);
lean_ctor_set(v___x_2637_, 11, v_currMacroScope_2630_);
lean_ctor_set(v___x_2637_, 12, v_cancelTk_x3f_2632_);
lean_ctor_set(v___x_2637_, 13, v_inheritedTraceOptions_2634_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*14, v_diag_2631_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*14 + 1, v_suppressElabErrors_2633_);
v___x_2638_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2618_, v___x_2635_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v___x_2637_, v_a_2611_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; lean_object* v_a_2641_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; uint8_t v___x_2736_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_2639_, v_a_2609_);
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
v___x_2736_ = l_Lean_Expr_hasSorry(v_a_2641_);
if (v___x_2736_ == 0)
{
v___y_2681_ = v_a_2606_;
v___y_2682_ = v_a_2607_;
v___y_2683_ = v_a_2608_;
v___y_2684_ = v_a_2609_;
v___y_2685_ = v___x_2637_;
v___y_2686_ = v_a_2611_;
goto v___jp_2680_;
}
else
{
uint8_t v___x_2737_; 
v___x_2737_ = l_Lean_Expr_hasSyntheticSorry(v_a_2641_);
if (v___x_2737_ == 0)
{
v___y_2718_ = v_a_2606_;
v___y_2719_ = v_a_2607_;
v___y_2720_ = v_a_2608_;
v___y_2721_ = v_a_2609_;
v___y_2722_ = v___x_2637_;
v___y_2723_ = v_a_2611_;
goto v___jp_2717_;
}
else
{
lean_object* v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2641_);
lean_dec_ref_known(v___x_2637_, 14);
v___x_2738_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
v___jp_2642_:
{
if (v___y_2652_ == 0)
{
if (lean_obj_tag(v___y_2645_) == 0)
{
lean_dec_ref_known(v___y_2645_, 2);
lean_dec_ref(v___y_2648_);
lean_dec(v_a_2641_);
return v___y_2644_;
}
else
{
lean_object* v_id_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2666_; 
v_id_2653_ = lean_ctor_get(v___y_2645_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___y_2645_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___y_2645_, 1);
lean_dec(v_unused_2667_);
v___x_2655_ = v___y_2645_;
v_isShared_2656_ = v_isSharedCheck_2666_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_id_2653_);
lean_dec(v___y_2645_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2666_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint8_t v___x_2657_; 
v___x_2657_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2650_, v_id_2653_);
lean_dec(v_id_2653_);
if (v___x_2657_ == 0)
{
lean_del_object(v___x_2655_);
lean_dec_ref(v___y_2648_);
lean_dec(v_a_2641_);
return v___y_2644_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec_ref(v___y_2644_);
v___x_2658_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_2659_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_2660_ = l_Lean_indentExpr(v_a_2641_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 7);
lean_ctor_set(v___x_2655_, 1, v___x_2660_);
lean_ctor_set(v___x_2655_, 0, v___x_2659_);
v___x_2662_ = v___x_2655_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
lean_ctor_set(v___x_2663_, 1, v___x_2658_);
v___x_2664_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2663_, v___y_2651_, v___y_2646_, v___y_2643_, v___y_2649_, v___y_2648_, v___y_2647_);
lean_dec_ref(v___y_2648_);
return v___x_2664_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2648_);
lean_dec_ref(v___y_2645_);
lean_dec(v_a_2641_);
return v___y_2644_;
}
}
v___jp_2668_:
{
lean_object* v___x_2675_; 
lean_inc(v_a_2641_);
v___x_2675_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2641_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_dec_ref(v___y_2673_);
lean_dec(v_a_2641_);
return v___x_2675_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
v___x_2677_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2678_ = l_Lean_Exception_isInterrupt(v_a_2676_);
if (v___x_2678_ == 0)
{
uint8_t v___x_2679_; 
lean_inc(v_a_2676_);
v___x_2679_ = l_Lean_Exception_isRuntime(v_a_2676_);
v___y_2643_ = v___y_2671_;
v___y_2644_ = v___x_2675_;
v___y_2645_ = v_a_2676_;
v___y_2646_ = v___y_2670_;
v___y_2647_ = v___y_2674_;
v___y_2648_ = v___y_2673_;
v___y_2649_ = v___y_2672_;
v___y_2650_ = v___x_2677_;
v___y_2651_ = v___y_2669_;
v___y_2652_ = v___x_2679_;
goto v___jp_2642_;
}
else
{
v___y_2643_ = v___y_2671_;
v___y_2644_ = v___x_2675_;
v___y_2645_ = v_a_2676_;
v___y_2646_ = v___y_2670_;
v___y_2647_ = v___y_2674_;
v___y_2648_ = v___y_2673_;
v___y_2649_ = v___y_2672_;
v___y_2650_ = v___x_2677_;
v___y_2651_ = v___y_2669_;
v___y_2652_ = v___x_2678_;
goto v___jp_2642_;
}
}
}
v___jp_2680_:
{
lean_object* v___x_2687_; 
lean_inc(v_a_2641_);
v___x_2687_ = l_Lean_Meta_getMVars(v_a_2641_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2688_, v___x_2615_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v_a_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; uint8_t v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = lean_unbox(v_a_2690_);
lean_dec(v_a_2690_);
if (v___x_2691_ == 0)
{
v___y_2669_ = v___y_2681_;
v___y_2670_ = v___y_2682_;
v___y_2671_ = v___y_2683_;
v___y_2672_ = v___y_2684_;
v___y_2673_ = v___y_2685_;
v___y_2674_ = v___y_2686_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2692_; lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v___y_2685_);
lean_dec(v_a_2641_);
v___x_2692_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v___y_2685_);
lean_dec(v_a_2641_);
v_a_2701_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2689_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2689_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v___y_2685_);
lean_dec(v_a_2641_);
v_a_2709_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2687_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2687_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
v___jp_2717_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v___x_2724_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_2725_ = l_Lean_indentExpr(v_a_2641_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2726_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec_ref(v___y_2722_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec_ref_known(v___x_2637_, 14);
v_a_2747_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2638_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2638_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_stx_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(lean_object* v_config_2766_, lean_object* v_item_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_item_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2786_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2767_, v___x_2785_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2786_) == 0)
{
uint8_t v___x_2787_; 
lean_dec_ref_known(v___x_2786_, 1);
v___x_2787_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_2767_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2788_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_2767_);
lean_inc_ref(v_item_2767_);
v___x_2789_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_2767_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_2791_ = lean_string_dec_lt(v___x_2788_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_2793_ = lean_string_dec_lt(v___x_2788_, v___x_2792_);
if (v___x_2793_ == 0)
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_string_dec_eq(v___x_2788_, v___x_2792_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_2796_ = lean_string_dec_eq(v___x_2788_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_2798_ = lean_string_dec_eq(v___x_2788_, v___x_2797_);
lean_dec_ref(v___x_2788_);
if (v___x_2798_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_2800_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_2799_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2800_) == 0)
{
uint8_t v___x_2801_; 
lean_dec_ref_known(v___x_2800_, 1);
v___x_2801_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_2801_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v___x_2789_);
v___x_2802_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2828_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2828_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2828_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
uint8_t v_proofs_2807_; uint8_t v_types_2808_; uint8_t v_implicits_2809_; uint8_t v_descend_2810_; uint8_t v_underBinder_2811_; uint8_t v_merge_2812_; uint8_t v_useContext_2813_; uint8_t v_onlyGivenNames_2814_; uint8_t v_preserveBinderNames_2815_; uint8_t v_lift_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2827_; 
v_proofs_2807_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_2808_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_2809_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_2810_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_2811_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_merge_2812_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_2813_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_2814_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_2815_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_2816_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2818_ = v_config_2766_;
v_isShared_2819_ = v_isSharedCheck_2827_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_config_2766_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2827_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, 0, v_proofs_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, 1, v_types_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, 2, v_implicits_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, 3, v_descend_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, 4, v_underBinder_2811_);
v___x_2821_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
uint8_t v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_unbox(v_a_2803_);
lean_dec(v_a_2803_);
lean_ctor_set_uint8(v___x_2821_, 5, v___x_2822_);
lean_ctor_set_uint8(v___x_2821_, 6, v_merge_2812_);
lean_ctor_set_uint8(v___x_2821_, 7, v_useContext_2813_);
lean_ctor_set_uint8(v___x_2821_, 8, v_onlyGivenNames_2814_);
lean_ctor_set_uint8(v___x_2821_, 9, v_preserveBinderNames_2815_);
lean_ctor_set_uint8(v___x_2821_, 10, v_lift_2816_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2821_);
v___x_2824_ = v___x_2805_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2821_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_config_2766_);
v_a_2829_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2802_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2802_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_2837_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2800_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2800_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v___x_2788_);
v___x_2845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_2846_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_2845_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2846_) == 0)
{
uint8_t v___x_2847_; 
lean_dec_ref_known(v___x_2846_, 1);
v___x_2847_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_2847_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2848_; 
lean_dec_ref(v___x_2789_);
v___x_2848_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2874_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2874_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2874_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
uint8_t v_proofs_2853_; uint8_t v_types_2854_; uint8_t v_implicits_2855_; uint8_t v_descend_2856_; uint8_t v_underBinder_2857_; uint8_t v_usedOnly_2858_; uint8_t v_merge_2859_; uint8_t v_onlyGivenNames_2860_; uint8_t v_preserveBinderNames_2861_; uint8_t v_lift_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2873_; 
v_proofs_2853_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_2854_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_2855_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_2856_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_2857_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_2858_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_2859_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_onlyGivenNames_2860_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_2861_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_2862_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2864_ = v_config_2766_;
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v_config_2766_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 0, v_proofs_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 1, v_types_2854_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 2, v_implicits_2855_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 3, v_descend_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 4, v_underBinder_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 5, v_usedOnly_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, 6, v_merge_2859_);
v___x_2867_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
uint8_t v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unbox(v_a_2849_);
lean_dec(v_a_2849_);
lean_ctor_set_uint8(v___x_2867_, 7, v___x_2868_);
lean_ctor_set_uint8(v___x_2867_, 8, v_onlyGivenNames_2860_);
lean_ctor_set_uint8(v___x_2867_, 9, v_preserveBinderNames_2861_);
lean_ctor_set_uint8(v___x_2867_, 10, v_lift_2862_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2867_);
v___x_2870_ = v___x_2851_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2867_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_config_2766_);
v_a_2875_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2848_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2848_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_2883_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2846_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2846_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec_ref(v___x_2788_);
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_2892_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_2891_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2892_) == 0)
{
uint8_t v___x_2893_; 
lean_dec_ref_known(v___x_2892_, 1);
v___x_2893_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_2893_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2894_; 
lean_dec_ref(v___x_2789_);
v___x_2894_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2920_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2920_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2920_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
uint8_t v_proofs_2899_; uint8_t v_types_2900_; uint8_t v_implicits_2901_; uint8_t v_descend_2902_; uint8_t v_usedOnly_2903_; uint8_t v_merge_2904_; uint8_t v_useContext_2905_; uint8_t v_onlyGivenNames_2906_; uint8_t v_preserveBinderNames_2907_; uint8_t v_lift_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2919_; 
v_proofs_2899_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_2900_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_2901_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_2902_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_usedOnly_2903_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_2904_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_2905_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_2906_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_2907_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_2908_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2910_ = v_config_2766_;
v_isShared_2911_ = v_isSharedCheck_2919_;
goto v_resetjp_2909_;
}
else
{
lean_dec(v_config_2766_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2919_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, 0, v_proofs_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, 1, v_types_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, 2, v_implicits_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, 3, v_descend_2902_);
v___x_2913_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
uint8_t v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = lean_unbox(v_a_2895_);
lean_dec(v_a_2895_);
lean_ctor_set_uint8(v___x_2913_, 4, v___x_2914_);
lean_ctor_set_uint8(v___x_2913_, 5, v_usedOnly_2903_);
lean_ctor_set_uint8(v___x_2913_, 6, v_merge_2904_);
lean_ctor_set_uint8(v___x_2913_, 7, v_useContext_2905_);
lean_ctor_set_uint8(v___x_2913_, 8, v_onlyGivenNames_2906_);
lean_ctor_set_uint8(v___x_2913_, 9, v_preserveBinderNames_2907_);
lean_ctor_set_uint8(v___x_2913_, 10, v_lift_2908_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2913_);
v___x_2916_ = v___x_2897_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2913_);
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
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_config_2766_);
v_a_2921_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2894_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2894_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_2929_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2892_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2892_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
else
{
uint8_t v___x_2937_; 
v___x_2937_ = lean_string_dec_eq(v___x_2788_, v___x_2790_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_2939_ = lean_string_dec_eq(v___x_2788_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_2941_ = lean_string_dec_eq(v___x_2788_, v___x_2940_);
lean_dec_ref(v___x_2788_);
if (v___x_2941_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_2943_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_2942_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2943_) == 0)
{
uint8_t v___x_2944_; 
lean_dec_ref_known(v___x_2943_, 1);
v___x_2944_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_2944_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2945_; 
lean_dec_ref(v___x_2789_);
v___x_2945_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2971_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2971_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2971_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
uint8_t v_proofs_2950_; uint8_t v_implicits_2951_; uint8_t v_descend_2952_; uint8_t v_underBinder_2953_; uint8_t v_usedOnly_2954_; uint8_t v_merge_2955_; uint8_t v_useContext_2956_; uint8_t v_onlyGivenNames_2957_; uint8_t v_preserveBinderNames_2958_; uint8_t v_lift_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2970_; 
v_proofs_2950_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_implicits_2951_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_2952_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_2953_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_2954_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_2955_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_2956_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_2957_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_2958_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_2959_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2961_ = v_config_2766_;
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v_config_2766_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 0, v_proofs_2950_);
v___x_2964_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
uint8_t v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_unbox(v_a_2946_);
lean_dec(v_a_2946_);
lean_ctor_set_uint8(v___x_2964_, 1, v___x_2965_);
lean_ctor_set_uint8(v___x_2964_, 2, v_implicits_2951_);
lean_ctor_set_uint8(v___x_2964_, 3, v_descend_2952_);
lean_ctor_set_uint8(v___x_2964_, 4, v_underBinder_2953_);
lean_ctor_set_uint8(v___x_2964_, 5, v_usedOnly_2954_);
lean_ctor_set_uint8(v___x_2964_, 6, v_merge_2955_);
lean_ctor_set_uint8(v___x_2964_, 7, v_useContext_2956_);
lean_ctor_set_uint8(v___x_2964_, 8, v_onlyGivenNames_2957_);
lean_ctor_set_uint8(v___x_2964_, 9, v_preserveBinderNames_2958_);
lean_ctor_set_uint8(v___x_2964_, 10, v_lift_2959_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2964_);
v___x_2967_ = v___x_2948_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2964_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec_ref(v_config_2766_);
v_a_2972_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2945_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2945_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_2980_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2943_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2943_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v___x_2788_);
v___x_2988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_2989_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_2988_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2989_) == 0)
{
uint8_t v___x_2990_; 
lean_dec_ref_known(v___x_2989_, 1);
v___x_2990_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_2990_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2991_; 
lean_dec_ref(v___x_2789_);
v___x_2991_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3017_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3017_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3017_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
uint8_t v_types_2996_; uint8_t v_implicits_2997_; uint8_t v_descend_2998_; uint8_t v_underBinder_2999_; uint8_t v_usedOnly_3000_; uint8_t v_merge_3001_; uint8_t v_useContext_3002_; uint8_t v_onlyGivenNames_3003_; uint8_t v_preserveBinderNames_3004_; uint8_t v_lift_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3016_; 
v_types_2996_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_2997_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_2998_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_2999_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3000_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3001_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3002_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3003_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_3004_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_3005_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3007_ = v_config_2766_;
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v_config_2766_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 0, 11);
v___x_3010_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
uint8_t v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
lean_ctor_set_uint8(v___x_3010_, 0, v___x_3011_);
lean_ctor_set_uint8(v___x_3010_, 1, v_types_2996_);
lean_ctor_set_uint8(v___x_3010_, 2, v_implicits_2997_);
lean_ctor_set_uint8(v___x_3010_, 3, v_descend_2998_);
lean_ctor_set_uint8(v___x_3010_, 4, v_underBinder_2999_);
lean_ctor_set_uint8(v___x_3010_, 5, v_usedOnly_3000_);
lean_ctor_set_uint8(v___x_3010_, 6, v_merge_3001_);
lean_ctor_set_uint8(v___x_3010_, 7, v_useContext_3002_);
lean_ctor_set_uint8(v___x_3010_, 8, v_onlyGivenNames_3003_);
lean_ctor_set_uint8(v___x_3010_, 9, v_preserveBinderNames_3004_);
lean_ctor_set_uint8(v___x_3010_, 10, v_lift_3005_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_3010_);
v___x_3013_ = v___x_2994_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3010_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v_config_2766_);
v_a_3018_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2991_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2991_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3026_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2989_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2989_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v___x_2788_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_3035_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3034_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3035_) == 0)
{
uint8_t v___x_3036_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3036_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3037_; 
lean_dec_ref(v___x_2789_);
v___x_3037_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3063_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3063_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3063_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
uint8_t v_proofs_3042_; uint8_t v_types_3043_; uint8_t v_implicits_3044_; uint8_t v_descend_3045_; uint8_t v_underBinder_3046_; uint8_t v_usedOnly_3047_; uint8_t v_merge_3048_; uint8_t v_useContext_3049_; uint8_t v_onlyGivenNames_3050_; uint8_t v_lift_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3062_; 
v_proofs_3042_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3043_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_3044_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_3045_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_3046_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3047_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3048_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3049_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3050_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_lift_3051_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3053_ = v_config_2766_;
v_isShared_3054_ = v_isSharedCheck_3062_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v_config_2766_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3062_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 0, v_proofs_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 1, v_types_3043_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 2, v_implicits_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 3, v_descend_3045_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 4, v_underBinder_3046_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 5, v_usedOnly_3047_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 6, v_merge_3048_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 7, v_useContext_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, 8, v_onlyGivenNames_3050_);
v___x_3056_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
uint8_t v___x_3057_; lean_object* v___x_3059_; 
v___x_3057_ = lean_unbox(v_a_3038_);
lean_dec(v_a_3038_);
lean_ctor_set_uint8(v___x_3056_, 9, v___x_3057_);
lean_ctor_set_uint8(v___x_3056_, 10, v_lift_3051_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3056_);
v___x_3059_ = v___x_3040_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3056_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_config_2766_);
v_a_3064_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3037_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3037_);
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
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3072_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3035_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3035_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
}
else
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_3081_ = lean_string_dec_lt(v___x_2788_, v___x_3080_);
if (v___x_3081_ == 0)
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_string_dec_eq(v___x_2788_, v___x_3080_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_3084_ = lean_string_dec_eq(v___x_2788_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_3086_ = lean_string_dec_eq(v___x_2788_, v___x_3085_);
lean_dec_ref(v___x_2788_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_3088_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3087_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3088_) == 0)
{
uint8_t v___x_3089_; 
lean_dec_ref_known(v___x_3088_, 1);
v___x_3089_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3089_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3090_; 
lean_dec_ref(v___x_2789_);
v___x_3090_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3116_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3116_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3116_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
uint8_t v_proofs_3095_; uint8_t v_types_3096_; uint8_t v_implicits_3097_; uint8_t v_descend_3098_; uint8_t v_underBinder_3099_; uint8_t v_usedOnly_3100_; uint8_t v_merge_3101_; uint8_t v_useContext_3102_; uint8_t v_preserveBinderNames_3103_; uint8_t v_lift_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3115_; 
v_proofs_3095_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3096_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_3097_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_3098_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_3099_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3100_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3101_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3102_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_preserveBinderNames_3103_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_3104_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3106_ = v_config_2766_;
v_isShared_3107_ = v_isSharedCheck_3115_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v_config_2766_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3115_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 0, v_proofs_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 1, v_types_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 2, v_implicits_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 3, v_descend_3098_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 4, v_underBinder_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 5, v_usedOnly_3100_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 6, v_merge_3101_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, 7, v_useContext_3102_);
v___x_3109_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
uint8_t v___x_3110_; lean_object* v___x_3112_; 
v___x_3110_ = lean_unbox(v_a_3091_);
lean_dec(v_a_3091_);
lean_ctor_set_uint8(v___x_3109_, 8, v___x_3110_);
lean_ctor_set_uint8(v___x_3109_, 9, v_preserveBinderNames_3103_);
lean_ctor_set_uint8(v___x_3109_, 10, v_lift_3104_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3109_);
v___x_3112_ = v___x_3093_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3109_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_config_2766_);
v_a_3117_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3090_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3090_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3125_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3088_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3088_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v___x_2788_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_3134_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3133_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3134_) == 0)
{
uint8_t v___x_3135_; 
lean_dec_ref_known(v___x_3134_, 1);
v___x_3135_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3135_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3136_; 
lean_dec_ref(v___x_2789_);
v___x_3136_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3162_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3162_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3162_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint8_t v_proofs_3141_; uint8_t v_types_3142_; uint8_t v_implicits_3143_; uint8_t v_descend_3144_; uint8_t v_underBinder_3145_; uint8_t v_usedOnly_3146_; uint8_t v_useContext_3147_; uint8_t v_onlyGivenNames_3148_; uint8_t v_preserveBinderNames_3149_; uint8_t v_lift_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3161_; 
v_proofs_3141_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3142_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_3143_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_3144_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_3145_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3146_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_useContext_3147_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3148_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_3149_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_3150_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3152_ = v_config_2766_;
v_isShared_3153_ = v_isSharedCheck_3161_;
goto v_resetjp_3151_;
}
else
{
lean_dec(v_config_2766_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3161_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 0, v_proofs_3141_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 1, v_types_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 2, v_implicits_3143_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 3, v_descend_3144_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 4, v_underBinder_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, 5, v_usedOnly_3146_);
v___x_3155_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
uint8_t v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_unbox(v_a_3137_);
lean_dec(v_a_3137_);
lean_ctor_set_uint8(v___x_3155_, 6, v___x_3156_);
lean_ctor_set_uint8(v___x_3155_, 7, v_useContext_3147_);
lean_ctor_set_uint8(v___x_3155_, 8, v_onlyGivenNames_3148_);
lean_ctor_set_uint8(v___x_3155_, 9, v_preserveBinderNames_3149_);
lean_ctor_set_uint8(v___x_3155_, 10, v_lift_3150_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3155_);
v___x_3158_ = v___x_3139_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3155_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v_config_2766_);
v_a_3163_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3136_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3136_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3171_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3134_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3134_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref(v___x_2788_);
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_3180_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3179_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3180_) == 0)
{
uint8_t v___x_3181_; 
lean_dec_ref_known(v___x_3180_, 1);
v___x_3181_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3181_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3182_; 
lean_dec_ref(v___x_2789_);
v___x_3182_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3208_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3208_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3208_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
uint8_t v_proofs_3187_; uint8_t v_types_3188_; uint8_t v_implicits_3189_; uint8_t v_descend_3190_; uint8_t v_underBinder_3191_; uint8_t v_usedOnly_3192_; uint8_t v_merge_3193_; uint8_t v_useContext_3194_; uint8_t v_onlyGivenNames_3195_; uint8_t v_preserveBinderNames_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3207_; 
v_proofs_3187_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3188_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_3189_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_descend_3190_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_3191_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3192_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3193_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3194_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3195_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_3196_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3198_ = v_config_2766_;
v_isShared_3199_ = v_isSharedCheck_3207_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v_config_2766_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3207_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 0, v_proofs_3187_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 1, v_types_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 2, v_implicits_3189_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 3, v_descend_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 4, v_underBinder_3191_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 5, v_usedOnly_3192_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 6, v_merge_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 7, v_useContext_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 8, v_onlyGivenNames_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3206_, 9, v_preserveBinderNames_3196_);
v___x_3201_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
uint8_t v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = lean_unbox(v_a_3183_);
lean_dec(v_a_3183_);
lean_ctor_set_uint8(v___x_3201_, 10, v___x_3202_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3201_);
v___x_3204_ = v___x_3185_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3201_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_config_2766_);
v_a_3209_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3182_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3182_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3217_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3180_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3180_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
}
else
{
lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_3226_ = lean_string_dec_eq(v___x_2788_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_3228_ = lean_string_dec_eq(v___x_2788_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_3230_ = lean_string_dec_eq(v___x_2788_, v___x_3229_);
lean_dec_ref(v___x_2788_);
if (v___x_3230_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_3232_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3231_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3232_) == 0)
{
uint8_t v___x_3233_; 
lean_dec_ref_known(v___x_3232_, 1);
v___x_3233_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3233_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3234_; 
lean_dec_ref(v___x_2789_);
v___x_3234_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3260_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3260_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3260_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
uint8_t v_proofs_3239_; uint8_t v_types_3240_; uint8_t v_descend_3241_; uint8_t v_underBinder_3242_; uint8_t v_usedOnly_3243_; uint8_t v_merge_3244_; uint8_t v_useContext_3245_; uint8_t v_onlyGivenNames_3246_; uint8_t v_preserveBinderNames_3247_; uint8_t v_lift_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3259_; 
v_proofs_3239_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3240_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_descend_3241_ = lean_ctor_get_uint8(v_config_2766_, 3);
v_underBinder_3242_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3243_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3244_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3245_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3246_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_3247_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_3248_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3250_ = v_config_2766_;
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
else
{
lean_dec(v_config_2766_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3258_, 0, v_proofs_3239_);
lean_ctor_set_uint8(v_reuseFailAlloc_3258_, 1, v_types_3240_);
v___x_3253_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
uint8_t v___x_3254_; lean_object* v___x_3256_; 
v___x_3254_ = lean_unbox(v_a_3235_);
lean_dec(v_a_3235_);
lean_ctor_set_uint8(v___x_3253_, 2, v___x_3254_);
lean_ctor_set_uint8(v___x_3253_, 3, v_descend_3241_);
lean_ctor_set_uint8(v___x_3253_, 4, v_underBinder_3242_);
lean_ctor_set_uint8(v___x_3253_, 5, v_usedOnly_3243_);
lean_ctor_set_uint8(v___x_3253_, 6, v_merge_3244_);
lean_ctor_set_uint8(v___x_3253_, 7, v_useContext_3245_);
lean_ctor_set_uint8(v___x_3253_, 8, v_onlyGivenNames_3246_);
lean_ctor_set_uint8(v___x_3253_, 9, v_preserveBinderNames_3247_);
lean_ctor_set_uint8(v___x_3253_, 10, v_lift_3248_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3253_);
v___x_3256_ = v___x_3237_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3253_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v_config_2766_);
v_a_3261_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3234_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3234_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3269_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3232_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3232_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec_ref(v___x_2788_);
v___x_3277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_3278_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2767_, v___x_3277_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3278_) == 0)
{
uint8_t v___x_3279_; 
lean_dec_ref_known(v___x_3278_, 1);
v___x_3279_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3279_ == 0)
{
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref(v___x_2789_);
v___x_3280_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3306_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
uint8_t v_proofs_3285_; uint8_t v_types_3286_; uint8_t v_implicits_3287_; uint8_t v_underBinder_3288_; uint8_t v_usedOnly_3289_; uint8_t v_merge_3290_; uint8_t v_useContext_3291_; uint8_t v_onlyGivenNames_3292_; uint8_t v_preserveBinderNames_3293_; uint8_t v_lift_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3305_; 
v_proofs_3285_ = lean_ctor_get_uint8(v_config_2766_, 0);
v_types_3286_ = lean_ctor_get_uint8(v_config_2766_, 1);
v_implicits_3287_ = lean_ctor_get_uint8(v_config_2766_, 2);
v_underBinder_3288_ = lean_ctor_get_uint8(v_config_2766_, 4);
v_usedOnly_3289_ = lean_ctor_get_uint8(v_config_2766_, 5);
v_merge_3290_ = lean_ctor_get_uint8(v_config_2766_, 6);
v_useContext_3291_ = lean_ctor_get_uint8(v_config_2766_, 7);
v_onlyGivenNames_3292_ = lean_ctor_get_uint8(v_config_2766_, 8);
v_preserveBinderNames_3293_ = lean_ctor_get_uint8(v_config_2766_, 9);
v_lift_3294_ = lean_ctor_get_uint8(v_config_2766_, 10);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_config_2766_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3296_ = v_config_2766_;
v_isShared_3297_ = v_isSharedCheck_3305_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v_config_2766_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3305_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, 0, v_proofs_3285_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, 1, v_types_3286_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, 2, v_implicits_3287_);
v___x_3299_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
uint8_t v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_unbox(v_a_3281_);
lean_dec(v_a_3281_);
lean_ctor_set_uint8(v___x_3299_, 3, v___x_3300_);
lean_ctor_set_uint8(v___x_3299_, 4, v_underBinder_3288_);
lean_ctor_set_uint8(v___x_3299_, 5, v_usedOnly_3289_);
lean_ctor_set_uint8(v___x_3299_, 6, v_merge_3290_);
lean_ctor_set_uint8(v___x_3299_, 7, v_useContext_3291_);
lean_ctor_set_uint8(v___x_3299_, 8, v_onlyGivenNames_3292_);
lean_ctor_set_uint8(v___x_3299_, 9, v_preserveBinderNames_3293_);
lean_ctor_set_uint8(v___x_3299_, 10, v_lift_3294_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3299_);
v___x_3302_ = v___x_3283_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3299_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec_ref(v_config_2766_);
v_a_3307_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3280_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3280_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3315_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3278_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3278_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
else
{
uint8_t v___x_3323_; 
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_config_2766_);
v___x_3323_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2789_);
if (v___x_3323_ == 0)
{
lean_dec_ref(v_item_2767_);
v_item_2776_ = v___x_2789_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
else
{
lean_object* v_value_3324_; lean_object* v___x_3325_; 
lean_dec_ref(v___x_2789_);
v_value_3324_ = lean_ctor_get(v_item_2767_, 2);
lean_inc(v_value_3324_);
lean_dec_ref(v_item_2767_);
v___x_3325_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_value_3324_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_3325_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_2766_);
v_item_2776_ = v_item_2767_;
v___y_2777_ = v___y_2768_;
v___y_2778_ = v___y_2769_;
v___y_2779_ = v___y_2770_;
v___y_2780_ = v___y_2771_;
v___y_2781_ = v___y_2772_;
v___y_2782_ = v___y_2773_;
goto v___jp_2775_;
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v_item_2767_);
lean_dec_ref(v_config_2766_);
v_a_3326_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_2786_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_2786_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
v___jp_2775_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_2784_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_2776_, v___x_2783_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3334_, lean_object* v_item_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(v_config_3334_, v_item_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
return v_res_3343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = lean_box(0);
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_3348_ = l_Lean_mkConst(v___x_3347_, v___x_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(lean_object* v_cfg_3351_, lean_object* v_cfgItem_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1);
v___x_3361_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3351_, v_cfgItem_3352_, v___x_3360_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_3362_, lean_object* v_cfgItem_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(v_cfg_3362_, v_cfgItem_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v_cfgItem_3363_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_cfg_3373_, lean_object* v_init_3374_, uint8_t v_logExceptions_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_onErr_3380_; lean_object* v_eval_3381_; 
v_onErr_3380_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0));
v_eval_3381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_3375_ == 0)
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3381_, v_init_3374_, v_cfg_3373_, v_onErr_3380_, v_logExceptions_3375_, v_a_3377_, v_a_3378_);
return v___x_3382_;
}
else
{
uint8_t v_recover_3383_; lean_object* v___x_3384_; 
v_recover_3383_ = lean_ctor_get_uint8(v_a_3376_, sizeof(void*)*1);
v___x_3384_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3381_, v_init_3374_, v_cfg_3373_, v_onErr_3380_, v_recover_3383_, v_a_3377_, v_a_3378_);
return v___x_3384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_cfg_3385_, lean_object* v_init_3386_, lean_object* v_logExceptions_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
uint8_t v_logExceptions_boxed_3392_; lean_object* v_res_3393_; 
v_logExceptions_boxed_3392_ = lean_unbox(v_logExceptions_3387_);
v_res_3393_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3385_, v_init_3386_, v_logExceptions_boxed_3392_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec_ref(v_a_3388_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_cfg_3394_, lean_object* v_init_3395_, uint8_t v_logExceptions_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3394_, v_init_3395_, v_logExceptions_3396_, v_a_3397_, v_a_3403_, v_a_3404_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_cfg_3407_, lean_object* v_init_3408_, lean_object* v_logExceptions_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
uint8_t v_logExceptions_boxed_3419_; lean_object* v_res_3420_; 
v_logExceptions_boxed_3419_ = lean_unbox(v_logExceptions_3409_);
v_res_3420_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_cfg_3407_, v_init_3408_, v_logExceptions_boxed_3419_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
return v_res_3420_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_3435_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_3434_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v_x_3436_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3449_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_MVarId_liftLets(v_a_3458_, v_a_3447_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = lean_box(0);
v___x_3462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3462_, 0, v_a_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3462_, v___y_3449_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
return v___x_3463_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3459_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3459_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v_a_3447_);
v_a_3472_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3457_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3457_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_3513_, lean_object* v_a_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3516_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_3525_, v_h_3513_, v_a_3514_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = lean_box(0);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3529_, v___y_3516_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3530_;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3526_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3526_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_a_3514_);
lean_dec(v_h_3513_);
v_a_3539_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3524_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3524_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_3547_, lean_object* v_a_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_3547_, v_a_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_3559_, lean_object* v_h_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___f_3570_; lean_object* v___x_3571_; 
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3570_, 0, v_h_3560_);
lean_closure_set(v___f_3570_, 1, v_a_3559_);
v___x_3571_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3570_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_3572_, lean_object* v_h_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_3572_, v_h_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_3591_);
v___x_3618_ = l_Lean_Syntax_isOfKind(v_x_3591_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec(v_x_3591_);
v___x_3619_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3620_ = lean_unsigned_to_nat(1u);
v___x_3621_ = l_Lean_Syntax_getArg(v_x_3591_, v___x_3620_);
v___x_3622_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_3621_);
v___x_3623_ = l_Lean_Syntax_isOfKind(v___x_3621_, v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_dec(v___x_3621_);
lean_dec(v_x_3591_);
v___x_3624_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3624_;
}
else
{
lean_object* v___f_3625_; lean_object* v_loc_x3f_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___f_3625_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_3660_ = lean_unsigned_to_nat(2u);
v___x_3661_ = l_Lean_Syntax_getArg(v_x_3591_, v___x_3660_);
lean_dec(v_x_3591_);
v___x_3662_ = l_Lean_Syntax_isNone(v___x_3661_);
if (v___x_3662_ == 0)
{
uint8_t v___x_3663_; 
lean_inc(v___x_3661_);
v___x_3663_ = l_Lean_Syntax_matchesNull(v___x_3661_, v___x_3620_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec(v___x_3661_);
lean_dec(v___x_3621_);
v___x_3664_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3664_;
}
else
{
lean_object* v___x_3665_; lean_object* v_loc_x3f_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3665_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3666_ = l_Lean_Syntax_getArg(v___x_3661_, v___x_3665_);
lean_dec(v___x_3661_);
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3666_);
v___x_3668_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3666_, v___x_3667_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; 
lean_dec(v_loc_x3f_3666_);
lean_dec(v___x_3621_);
v___x_3669_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3669_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3670_, 0, v_loc_x3f_3666_);
v_loc_x3f_3627_ = v___x_3670_;
v___y_3628_ = v_a_3592_;
v___y_3629_ = v_a_3593_;
v___y_3630_ = v_a_3594_;
v___y_3631_ = v_a_3595_;
v___y_3632_ = v_a_3596_;
v___y_3633_ = v_a_3597_;
v___y_3634_ = v_a_3598_;
v___y_3635_ = v_a_3599_;
goto v___jp_3626_;
}
}
}
else
{
lean_object* v___x_3671_; 
lean_dec(v___x_3661_);
v___x_3671_ = lean_box(0);
v_loc_x3f_3627_ = v___x_3671_;
v___y_3628_ = v_a_3592_;
v___y_3629_ = v_a_3593_;
v___y_3630_ = v_a_3594_;
v___y_3631_ = v_a_3595_;
v___y_3632_ = v_a_3596_;
v___y_3633_ = v_a_3597_;
v___y_3634_ = v_a_3598_;
v___y_3635_ = v_a_3599_;
goto v___jp_3626_;
}
v___jp_3626_:
{
uint8_t v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = 0;
v___x_3637_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_3637_, 0, v___x_3636_);
lean_ctor_set_uint8(v___x_3637_, 1, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 2, v___x_3636_);
lean_ctor_set_uint8(v___x_3637_, 3, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 4, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 5, v___x_3636_);
lean_ctor_set_uint8(v___x_3637_, 6, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 7, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 8, v___x_3636_);
lean_ctor_set_uint8(v___x_3637_, 9, v___x_3623_);
lean_ctor_set_uint8(v___x_3637_, 10, v___x_3623_);
v___x_3638_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_3621_, v___x_3637_, v___x_3623_, v___y_3628_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___f_3642_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc_n(v_a_3639_, 2);
lean_dec_ref_known(v___x_3638_, 1);
v___f_3640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3640_, 0, v_a_3639_);
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3641_, 0, v___f_3640_);
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_3642_, 0, v_a_3639_);
if (lean_obj_tag(v_loc_x3f_3627_) == 0)
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_box(0);
v___y_3602_ = v___f_3641_;
v___y_3603_ = v___y_3634_;
v___y_3604_ = v___y_3628_;
v___y_3605_ = v___y_3633_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v___y_3635_;
v___y_3608_ = v___y_3629_;
v___y_3609_ = v___y_3631_;
v___y_3610_ = v___f_3642_;
v___y_3611_ = v___f_3625_;
v___y_3612_ = v___y_3632_;
v___y_3613_ = v___x_3643_;
goto v___jp_3601_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_val_3644_ = lean_ctor_get(v_loc_x3f_3627_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_loc_x3f_3627_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v_loc_x3f_3627_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v_loc_x3f_3627_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_val_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
v___y_3602_ = v___f_3641_;
v___y_3603_ = v___y_3634_;
v___y_3604_ = v___y_3628_;
v___y_3605_ = v___y_3633_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v___y_3635_;
v___y_3608_ = v___y_3629_;
v___y_3609_ = v___y_3631_;
v___y_3610_ = v___f_3642_;
v___y_3611_ = v___f_3625_;
v___y_3612_ = v___y_3632_;
v___y_3613_ = v___x_3649_;
goto v___jp_3601_;
}
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec(v_loc_x3f_3627_);
v_a_3652_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3638_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3638_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
}
v___jp_3601_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = l_Lean_mkOptionalNode(v___y_3613_);
v___x_3615_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3614_);
lean_dec(v___x_3614_);
lean_inc_ref(v___y_3611_);
v___x_3616_ = l_Lean_Elab_Tactic_withLocation(v___x_3615_, v___y_3610_, v___y_3602_, v___y_3611_, v___y_3604_, v___y_3608_, v___y_3606_, v___y_3609_, v___y_3612_, v___y_3605_, v___y_3603_, v___y_3607_);
lean_dec(v___x_3615_);
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3690_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_3693_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_3694_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3690_, v___x_3691_, v___x_3692_, v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_3696_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_3711_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_3710_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v_x_3712_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t v___x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3725_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l_Lean_MVarId_letToHave(v_a_3734_, v___x_3723_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3737_ = lean_box(0);
v___x_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3738_, 0, v_a_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3738_, v___y_3725_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3739_;
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
v_a_3740_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3735_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3735_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_a_3748_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3733_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3733_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v___x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
uint8_t v___x_1775__boxed_3766_; lean_object* v_res_3767_; 
v___x_1775__boxed_3766_ = lean_unbox(v___x_3756_);
v_res_3767_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v___x_1775__boxed_3766_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object* v_h_3768_, uint8_t v___x_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3771_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_3780_, v_h_3768_, v___x_3769_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = lean_box(0);
v___x_3784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3784_, 0, v_a_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3784_, v___y_3771_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3785_;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_a_3786_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3781_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3781_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_h_3768_);
v_a_3794_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3779_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3779_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v_h_3802_, lean_object* v___x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___x_1851__boxed_3813_; lean_object* v_res_3814_; 
v___x_1851__boxed_3813_ = lean_unbox(v___x_3803_);
v_res_3814_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v_h_3802_, v___x_1851__boxed_3813_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_3815_, lean_object* v_h_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; 
v___x_3826_ = lean_box(v___x_3815_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3827_, 0, v_h_3816_);
lean_closure_set(v___f_3827_, 1, v___x_3826_);
v___x_3828_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3827_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_3829_, lean_object* v_h_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
uint8_t v___x_1927__boxed_3840_; lean_object* v_res_3841_; 
v___x_1927__boxed_3840_ = lean_unbox(v___x_3829_);
v_res_3841_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1927__boxed_3840_, v_h_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_3849_);
v___x_3860_ = l_Lean_Syntax_isOfKind(v_x_3849_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v_x_3849_);
v___x_3861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3861_;
}
else
{
lean_object* v___f_3862_; lean_object* v___x_3863_; lean_object* v___f_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; lean_object* v___f_3867_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___f_3862_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_3863_ = lean_box(v___x_3860_);
v___f_3864_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3864_, 0, v___x_3863_);
v___f_3865_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3865_, 0, v___f_3864_);
v___x_3866_ = lean_box(v___x_3860_);
v___f_3867_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_3867_, 0, v___x_3866_);
v___x_3881_ = lean_unsigned_to_nat(1u);
v___x_3882_ = l_Lean_Syntax_getArg(v_x_3849_, v___x_3881_);
lean_dec(v_x_3849_);
v___x_3883_ = l_Lean_Syntax_isNone(v___x_3882_);
if (v___x_3883_ == 0)
{
uint8_t v___x_3884_; 
lean_inc(v___x_3882_);
v___x_3884_ = l_Lean_Syntax_matchesNull(v___x_3882_, v___x_3881_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec(v___x_3882_);
lean_dec_ref(v___f_3867_);
lean_dec_ref(v___f_3865_);
v___x_3885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; lean_object* v_loc_x3f_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3886_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3887_ = l_Lean_Syntax_getArg(v___x_3882_, v___x_3886_);
lean_dec(v___x_3882_);
v___x_3888_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3887_);
v___x_3889_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_dec(v_loc_x3f_3887_);
lean_dec_ref(v___f_3867_);
lean_dec_ref(v___f_3865_);
v___x_3890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3890_;
}
else
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v_loc_x3f_3887_);
v___y_3869_ = v_a_3854_;
v___y_3870_ = v_a_3857_;
v___y_3871_ = v_a_3853_;
v___y_3872_ = v_a_3852_;
v___y_3873_ = v_a_3856_;
v___y_3874_ = v_a_3850_;
v___y_3875_ = v_a_3855_;
v___y_3876_ = v_a_3851_;
v___y_3877_ = v___x_3891_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v___x_3892_; 
lean_dec(v___x_3882_);
v___x_3892_ = lean_box(0);
v___y_3869_ = v_a_3854_;
v___y_3870_ = v_a_3857_;
v___y_3871_ = v_a_3853_;
v___y_3872_ = v_a_3852_;
v___y_3873_ = v_a_3856_;
v___y_3874_ = v_a_3850_;
v___y_3875_ = v_a_3855_;
v___y_3876_ = v_a_3851_;
v___y_3877_ = v___x_3892_;
goto v___jp_3868_;
}
v___jp_3868_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = l_Lean_mkOptionalNode(v___y_3877_);
v___x_3879_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3878_);
lean_dec(v___x_3878_);
v___x_3880_ = l_Lean_Elab_Tactic_withLocation(v___x_3879_, v___f_3867_, v___f_3865_, v___f_3862_, v___y_3874_, v___y_3876_, v___y_3872_, v___y_3871_, v___y_3869_, v___y_3875_, v___y_3873_, v___y_3870_);
lean_dec(v___x_3879_);
return v___x_3880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3911_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3912_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_3913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_3914_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_3915_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3911_, v___x_3912_, v___x_3913_, v___x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_3917_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
