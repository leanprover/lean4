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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_letToHave(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_options_89_ = lean_ctor_get(v___y_81_, 1);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_106_, uint8_t v___y_107_, lean_object* v_x_108_){
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
return v___x_116_;
}
else
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_118_ = lean_string_dec_eq(v_str_111_, v___x_117_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
return v_suppressElabErrors_106_;
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
return v___x_120_;
}
else
{
return v_suppressElabErrors_106_;
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
return v___x_126_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_128_ = lean_string_dec_eq(v_str_123_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_130_ = lean_string_dec_eq(v_str_122_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
}
else
{
return v___y_107_;
}
}
default: 
{
return v___y_107_;
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
return v___x_133_;
}
else
{
return v_suppressElabErrors_106_;
}
}
default: 
{
return v___y_107_;
}
}
}
else
{
return v___y_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_134_, lean_object* v___y_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_suppressElabErrors_boxed_137_; uint8_t v___y_6698__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_suppressElabErrors_boxed_137_ = lean_unbox(v_suppressElabErrors_134_);
v___y_6698__boxed_138_ = lean_unbox(v___y_135_);
v_res_139_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_137_, v___y_6698__boxed_138_, v_x_136_);
lean_dec(v_x_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_142_, lean_object* v_msgData_143_, uint8_t v_severity_144_, uint8_t v_isSilent_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___y_152_; lean_object* v___y_153_; uint8_t v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_188_; lean_object* v___y_189_; uint8_t v___y_190_; uint8_t v___y_191_; uint8_t v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___y_217_; uint8_t v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_227_; uint8_t v___y_228_; uint8_t v___y_229_; uint8_t v___x_234_; lean_object* v___y_236_; lean_object* v___y_237_; uint8_t v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; uint8_t v___y_241_; uint8_t v___y_243_; uint8_t v___x_257_; 
v___x_234_ = 2;
v___x_257_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_234_);
if (v___x_257_ == 0)
{
v___y_243_ = v___x_257_;
goto v___jp_242_;
}
else
{
uint8_t v___x_258_; 
lean_inc_ref(v_msgData_143_);
v___x_258_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_143_);
v___y_243_ = v___x_258_;
goto v___jp_242_;
}
v___jp_151_:
{
lean_object* v___x_161_; lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v_env_164_; lean_object* v_nextMacroScope_165_; lean_object* v_ngen_166_; lean_object* v_auxDeclNGen_167_; lean_object* v_traceState_168_; lean_object* v_cache_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_186_; 
v___x_161_ = lean_st_ref_take(v___y_160_);
v_currNamespace_162_ = lean_ctor_get(v___y_159_, 5);
v_openDecls_163_ = lean_ctor_get(v___y_159_, 6);
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
lean_ctor_set(v___x_177_, 1, v___y_157_);
lean_inc_ref(v___y_158_);
lean_inc_ref(v___y_152_);
v___x_178_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_178_, 0, v___y_152_);
lean_ctor_set(v___x_178_, 1, v___y_153_);
lean_ctor_set(v___x_178_, 2, v___y_156_);
lean_ctor_set(v___x_178_, 3, v___y_158_);
lean_ctor_set(v___x_178_, 4, v___x_177_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5, v___y_155_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5 + 1, v___y_154_);
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
v___x_182_ = lean_st_ref_put(v___y_160_, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
v___jp_187_:
{
lean_object* v_fileName_195_; lean_object* v_fileMap_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
v_fileName_195_ = lean_ctor_get(v___y_189_, 0);
v_fileMap_196_ = lean_ctor_get(v___y_189_, 1);
v___x_197_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_143_);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_197_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref_n(v_fileMap_196_, 2);
v___x_203_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_193_);
lean_dec(v___y_193_);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_194_);
lean_dec(v___y_194_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_190_ == 0)
{
lean_del_object(v___x_201_);
lean_dec_ref(v___y_188_);
v___y_152_ = v_fileName_195_;
v___y_153_ = v___x_203_;
v___y_154_ = v___y_192_;
v___y_155_ = v___y_191_;
v___y_156_ = v___x_205_;
v___y_157_ = v_a_199_;
v___y_158_ = v___x_206_;
v___y_159_ = v___y_148_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
else
{
uint8_t v___x_207_; 
lean_inc(v_a_199_);
v___x_207_ = l_Lean_MessageData_hasTag(v___y_188_, v_a_199_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec_ref_known(v___x_205_, 1);
lean_dec_ref(v___x_203_);
lean_dec(v_a_199_);
v___x_208_ = lean_box(0);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_152_ = v_fileName_195_;
v___y_153_ = v___x_203_;
v___y_154_ = v___y_192_;
v___y_155_ = v___y_191_;
v___y_156_ = v___x_205_;
v___y_157_ = v_a_199_;
v___y_158_ = v___x_206_;
v___y_159_ = v___y_148_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
}
}
}
v___jp_213_:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_215_, v___y_218_);
lean_dec(v___y_215_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_188_ = v___y_214_;
v___y_189_ = v___y_216_;
v___y_190_ = v___y_219_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_220_;
v___y_194_ = v___y_220_;
goto v___jp_187_;
}
else
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___y_188_ = v___y_214_;
v___y_189_ = v___y_216_;
v___y_190_ = v___y_219_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_220_;
v___y_194_ = v_val_222_;
goto v___jp_187_;
}
}
v___jp_223_:
{
lean_object* v_ref_230_; lean_object* v___x_231_; 
v_ref_230_ = l_Lean_replaceRef(v_ref_142_, v___y_225_);
v___x_231_ = l_Lean_Syntax_getPos_x3f(v_ref_230_, v___y_228_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___y_214_ = v___y_224_;
v___y_215_ = v_ref_230_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_229_;
v___y_218_ = v___y_228_;
v___y_219_ = v___y_227_;
v___y_220_ = v___x_232_;
goto v___jp_213_;
}
else
{
lean_object* v_val_233_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_231_, 1);
v___y_214_ = v___y_224_;
v___y_215_ = v_ref_230_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_229_;
v___y_218_ = v___y_228_;
v___y_219_ = v___y_227_;
v___y_220_ = v_val_233_;
goto v___jp_213_;
}
}
v___jp_235_:
{
if (v___y_241_ == 0)
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_236_;
v___y_226_ = v___y_237_;
v___y_227_ = v___y_238_;
v___y_228_ = v___y_240_;
v___y_229_ = v_severity_144_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_236_;
v___y_226_ = v___y_237_;
v___y_227_ = v___y_238_;
v___y_228_ = v___y_240_;
v___y_229_ = v___x_234_;
goto v___jp_223_;
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_object* v_toCold_244_; lean_object* v_options_245_; lean_object* v_ref_246_; uint8_t v_suppressElabErrors_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___f_250_; uint8_t v___x_251_; uint8_t v___x_252_; 
v_toCold_244_ = lean_ctor_get(v___y_148_, 0);
v_options_245_ = lean_ctor_get(v___y_148_, 1);
v_ref_246_ = lean_ctor_get(v___y_148_, 4);
v_suppressElabErrors_247_ = lean_ctor_get_uint8(v___y_148_, sizeof(void*)*10 + 1);
v___x_248_ = lean_box(v_suppressElabErrors_247_);
v___x_249_ = lean_box(v___y_243_);
v___f_250_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_250_, 0, v___x_248_);
lean_closure_set(v___f_250_, 1, v___x_249_);
v___x_251_ = 1;
v___x_252_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_251_);
if (v___x_252_ == 0)
{
v___y_236_ = v_ref_246_;
v___y_237_ = v_toCold_244_;
v___y_238_ = v_suppressElabErrors_247_;
v___y_239_ = v___f_250_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_252_;
goto v___jp_235_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = l_Lean_warningAsError;
v___x_254_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_245_, v___x_253_);
v___y_236_ = v_ref_246_;
v___y_237_ = v_toCold_244_;
v___y_238_ = v_suppressElabErrors_247_;
v___y_239_ = v___f_250_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_254_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_msgData_143_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_259_, lean_object* v_msgData_260_, lean_object* v_severity_261_, lean_object* v_isSilent_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_severity_boxed_268_; uint8_t v_isSilent_boxed_269_; lean_object* v_res_270_; 
v_severity_boxed_268_ = lean_unbox(v_severity_261_);
v_isSilent_boxed_269_ = lean_unbox(v_isSilent_262_);
v_res_270_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_259_, v_msgData_260_, v_severity_boxed_268_, v_isSilent_boxed_269_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v_ref_259_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object* v_ref_271_, lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = 1;
v___x_283_ = 0;
v___x_284_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_271_, v_msgData_272_, v___x_282_, v___x_283_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object* v_ref_285_, lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_285_, v_msgData_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v_ref_285_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object* v_linterOption_303_, lean_object* v_stx_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_name_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_333_; 
v_name_315_ = lean_ctor_get(v_linterOption_303_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_linterOption_303_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_linterOption_303_, 1);
lean_dec(v_unused_334_);
v___x_317_ = v_linterOption_303_;
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_name_315_);
lean_dec(v_linterOption_303_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
lean_inc(v_name_315_);
v___x_320_ = l_Lean_MessageData_ofName(v_name_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 7);
lean_ctor_set(v___x_317_, 1, v___x_320_);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_332_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_disable_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_323_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v_disable_325_ = l_Lean_MessageData_note(v___x_324_);
v___x_326_ = l_Lean_Linter_linterMessageTag;
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v_msg_305_);
lean_ctor_set(v___x_327_, 1, v_disable_325_);
v___x_328_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_329_, 0, v_name_315_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
lean_inc(v_stx_304_);
v___x_330_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_330_, 0, v_stx_304_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_304_, v___x_330_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v_stx_304_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object* v_linterOption_335_, lean_object* v_stx_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_335_, v_stx_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v___x_353_; lean_object* v_toEnvExtension_354_; lean_object* v_asyncMode_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_merged_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v___x_351_ = lean_st_ref_get(v___y_349_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref(v_env_352_);
lean_dec(v___x_351_);
v___x_353_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_354_ = lean_ctor_get(v___x_353_, 0);
v_asyncMode_355_ = lean_ctor_get(v_toEnvExtension_354_, 2);
v___x_356_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_357_ = lean_box(0);
v___x_358_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_356_, v___x_353_, v_env_352_, v_asyncMode_355_, v___x_357_);
v_merged_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v___x_358_, 1);
lean_dec(v_unused_368_);
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_merged_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v_merged_359_);
lean_ctor_set(v___x_361_, 0, v_o_348_);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_o_348_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_merged_359_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_369_, v___y_370_);
lean_dec(v___y_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_options_382_; lean_object* v___x_383_; 
v_options_382_ = lean_ctor_get(v___y_379_, 1);
lean_inc_ref(v_options_382_);
v___x_383_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_382_, v___y_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_394_, lean_object* v_stx_395_, lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_417_; 
v___x_406_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_417_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_Linter_getLinterValue(v_linterOption_394_, v_a_407_);
lean_dec(v_a_407_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_dec_ref(v_msg_396_);
lean_dec(v_stx_395_);
lean_dec_ref(v_linterOption_394_);
v___x_412_ = lean_box(0);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_object* v___x_416_; 
lean_del_object(v___x_409_);
v___x_416_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_394_, v_stx_395_, v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_418_, lean_object* v_stx_419_, lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_418_, v_stx_419_, v_msg_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
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
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_434_, lean_object* v_fvars_435_, lean_object* v_ids_436_, lean_object* v_a_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_a_449_; uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_lt(v_a_437_, v_upperBound_434_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v_a_437_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_b_438_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_array_get_size(v_fvars_435_);
v___x_457_ = lean_nat_dec_lt(v_a_437_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_459_ = lean_array_fget_borrowed(v_ids_436_, v_a_437_);
v___x_460_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
lean_inc(v___x_459_);
v___x_461_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_458_, v___x_459_, v___x_460_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_dec_ref_known(v___x_461_, 1);
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
lean_dec(v_a_437_);
return v___x_461_;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_array_fget_borrowed(v_ids_436_, v_a_437_);
v___x_463_ = lean_array_fget_borrowed(v_fvars_435_, v_a_437_);
lean_inc(v___x_463_);
v___x_464_ = l_Lean_mkFVar(v___x_463_);
lean_inc(v___x_462_);
v___x_465_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_462_, v___x_464_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_dec_ref_known(v___x_465_, 1);
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
lean_dec(v_a_437_);
return v___x_465_;
}
}
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_a_437_, v___x_450_);
lean_dec(v_a_437_);
v_a_437_ = v___x_451_;
v_b_438_ = v_a_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_466_, lean_object* v_fvars_467_, lean_object* v_ids_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_466_, v_fvars_467_, v_ids_468_, v_a_469_, v_b_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec_ref(v_ids_468_);
lean_dec_ref(v_fvars_467_);
lean_dec(v_upperBound_466_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_481_, lean_object* v_fvars_482_, lean_object* v_ids_483_, lean_object* v___x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_481_, v_fvars_482_, v_ids_483_, v___x_494_, v___x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_495_, 0);
lean_dec(v_unused_503_);
v___x_497_ = v___x_495_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_dec(v___x_495_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_484_);
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_484_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_504_, lean_object* v_fvars_505_, lean_object* v_ids_506_, lean_object* v___x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_504_, v_fvars_505_, v_ids_506_, v___x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_ids_506_);
lean_dec_ref(v_fvars_505_);
lean_dec(v___x_504_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_518_, lean_object* v_fvars_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
v___x_529_ = lean_array_get_size(v_ids_518_);
v___x_530_ = lean_box(0);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_531_, 0, v___x_529_);
lean_closure_set(v___f_531_, 1, v_fvars_519_);
lean_closure_set(v___f_531_, 2, v_ids_518_);
lean_closure_set(v___f_531_, 3, v___x_530_);
v___x_532_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_531_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_533_, lean_object* v_fvars_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_533_, v_fvars_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_545_, lean_object* v_fvars_546_, lean_object* v_ids_547_, lean_object* v_inst_548_, lean_object* v_R_549_, lean_object* v_a_550_, lean_object* v_b_551_, lean_object* v_c_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_545_, v_fvars_546_, v_ids_547_, v_a_550_, v_b_551_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_563_ = _args[0];
lean_object* v_fvars_564_ = _args[1];
lean_object* v_ids_565_ = _args[2];
lean_object* v_inst_566_ = _args[3];
lean_object* v_R_567_ = _args[4];
lean_object* v_a_568_ = _args[5];
lean_object* v_b_569_ = _args[6];
lean_object* v_c_570_ = _args[7];
lean_object* v___y_571_ = _args[8];
lean_object* v___y_572_ = _args[9];
lean_object* v___y_573_ = _args[10];
lean_object* v___y_574_ = _args[11];
lean_object* v___y_575_ = _args[12];
lean_object* v___y_576_ = _args[13];
lean_object* v___y_577_ = _args[14];
lean_object* v___y_578_ = _args[15];
lean_object* v___y_579_ = _args[16];
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_563_, v_fvars_564_, v_ids_565_, v_inst_566_, v_R_567_, v_a_568_, v_b_569_, v_c_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_ids_565_);
lean_dec_ref(v_fvars_564_);
lean_dec(v_upperBound_563_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_581_, v___y_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_603_, lean_object* v_msgData_604_, uint8_t v_severity_605_, uint8_t v_isSilent_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_603_, v_msgData_604_, v_severity_605_, v_isSilent_606_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_617_, lean_object* v_msgData_618_, lean_object* v_severity_619_, lean_object* v_isSilent_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
uint8_t v_severity_boxed_630_; uint8_t v_isSilent_boxed_631_; lean_object* v_res_632_; 
v_severity_boxed_630_ = lean_unbox(v_severity_619_);
v_isSilent_boxed_631_ = lean_unbox(v_isSilent_620_);
v_res_632_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_617_, v_msgData_618_, v_severity_boxed_630_, v_isSilent_boxed_631_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v_ref_617_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(lean_object* v_00_u03b1_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(v_00_u03b1_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_ref_661_; lean_object* v___x_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_ref_661_ = lean_ctor_get(v___y_658_, 4);
v___x_662_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_inc(v_ref_661_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_ref_661_);
lean_ctor_set(v___x_667_, 1, v_a_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 1);
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object* v___x_683_, lean_object* v_ctor_684_, lean_object* v_args_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_844_ = lean_string_dec_eq(v_ctor_684_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_array_get_size(v_args_685_);
v___x_847_ = lean_unsigned_to_nat(11u);
v___x_848_ = lean_nat_dec_eq(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v___x_849_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_850_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_849_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
goto v___jp_691_;
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_692_);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_693_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_696_);
lean_inc(v___x_697_);
v___x_698_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_697_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = lean_unsigned_to_nat(2u);
v___x_701_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_700_);
lean_inc(v___x_701_);
v___x_702_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_701_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_unsigned_to_nat(3u);
v___x_705_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_704_);
lean_inc(v___x_705_);
v___x_706_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_705_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = lean_unsigned_to_nat(4u);
v___x_709_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_708_);
lean_inc(v___x_709_);
v___x_710_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_709_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_unsigned_to_nat(5u);
v___x_713_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_712_);
lean_inc(v___x_713_);
v___x_714_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_713_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_unsigned_to_nat(6u);
v___x_717_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_716_);
lean_inc(v___x_717_);
v___x_718_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_717_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_unsigned_to_nat(7u);
v___x_721_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_720_);
lean_inc(v___x_721_);
v___x_722_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_721_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_unsigned_to_nat(8u);
v___x_725_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_724_);
lean_inc(v___x_725_);
v___x_726_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_725_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = lean_unsigned_to_nat(9u);
v___x_729_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_728_);
lean_inc(v___x_729_);
v___x_730_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_729_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = lean_unsigned_to_nat(10u);
v___x_733_ = lean_array_get_borrowed(v___x_683_, v_args_685_, v___x_732_);
lean_inc(v___x_733_);
v___x_734_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_733_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_754_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_754_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint8_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; uint8_t v___x_750_; lean_object* v___x_752_; 
v___x_739_ = lean_alloc_ctor(0, 0, 11);
v___x_740_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
lean_ctor_set_uint8(v___x_739_, 0, v___x_740_);
v___x_741_ = lean_unbox(v_a_699_);
lean_dec(v_a_699_);
lean_ctor_set_uint8(v___x_739_, 1, v___x_741_);
v___x_742_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
lean_ctor_set_uint8(v___x_739_, 2, v___x_742_);
v___x_743_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
lean_ctor_set_uint8(v___x_739_, 3, v___x_743_);
v___x_744_ = lean_unbox(v_a_711_);
lean_dec(v_a_711_);
lean_ctor_set_uint8(v___x_739_, 4, v___x_744_);
v___x_745_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
lean_ctor_set_uint8(v___x_739_, 5, v___x_745_);
v___x_746_ = lean_unbox(v_a_719_);
lean_dec(v_a_719_);
lean_ctor_set_uint8(v___x_739_, 6, v___x_746_);
v___x_747_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
lean_ctor_set_uint8(v___x_739_, 7, v___x_747_);
v___x_748_ = lean_unbox(v_a_727_);
lean_dec(v_a_727_);
lean_ctor_set_uint8(v___x_739_, 8, v___x_748_);
v___x_749_ = lean_unbox(v_a_731_);
lean_dec(v_a_731_);
lean_ctor_set_uint8(v___x_739_, 9, v___x_749_);
v___x_750_ = lean_unbox(v_a_735_);
lean_dec(v_a_735_);
lean_ctor_set_uint8(v___x_739_, 10, v___x_750_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_752_ = v___x_737_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_739_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_731_);
lean_dec(v_a_727_);
lean_dec(v_a_723_);
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_755_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_734_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_734_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_727_);
lean_dec(v_a_723_);
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_763_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_730_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_730_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_a_723_);
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_771_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_726_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_726_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_779_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_722_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_722_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_787_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_718_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_718_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_795_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_714_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_714_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_803_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_710_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_710_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_811_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_706_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_706_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_819_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_702_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_702_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_695_);
v_a_827_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_698_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_698_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_694_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_694_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object* v___x_859_, lean_object* v_ctor_860_, lean_object* v_args_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(v___x_859_, v_ctor_860_, v_args_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_args_861_);
lean_dec_ref(v_ctor_860_);
lean_dec_ref(v___x_859_);
return v_res_867_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_868_; lean_object* v___f_869_; 
v___x_868_ = l_Lean_instInhabitedExpr;
v___f_869_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_869_, 0, v___x_868_);
return v___f_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___f_882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0);
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_884_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_883_, v___f_882_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(lean_object* v_00_u03b1_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(v_00_u03b1_900_, v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(0);
v___x_910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_911_ = l_Lean_Expr_const___override(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0));
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig(void){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Expr_hasMVar(v_e_918_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_e_918_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v_mctx_924_; lean_object* v___x_925_; lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___x_928_; lean_object* v_cache_929_; lean_object* v_zetaDeltaFVarIds_930_; lean_object* v_postponed_931_; lean_object* v_diag_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_941_; 
v___x_923_ = lean_st_ref_get(v___y_919_);
v_mctx_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc_ref(v_mctx_924_);
lean_dec(v___x_923_);
v___x_925_ = l_Lean_instantiateMVarsCore(v_mctx_924_, v_e_918_);
v_fst_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_fst_926_);
v_snd_927_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_snd_927_);
lean_dec_ref(v___x_925_);
v___x_928_ = lean_st_ref_take(v___y_919_);
v_cache_929_ = lean_ctor_get(v___x_928_, 1);
v_zetaDeltaFVarIds_930_ = lean_ctor_get(v___x_928_, 2);
v_postponed_931_ = lean_ctor_get(v___x_928_, 3);
v_diag_932_ = lean_ctor_get(v___x_928_, 4);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_942_);
v___x_934_ = v___x_928_;
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_diag_932_);
lean_inc(v_postponed_931_);
lean_inc(v_zetaDeltaFVarIds_930_);
lean_inc(v_cache_929_);
lean_dec(v___x_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_snd_927_);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_snd_927_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_cache_929_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_zetaDeltaFVarIds_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_postponed_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_diag_932_);
v___x_937_ = v_reuseFailAlloc_940_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_st_ref_put(v___y_919_, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_fst_926_);
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_943_, v___y_944_);
lean_dec(v___y_944_);
return v_res_946_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_box(1);
v___x_948_ = l_Lean_MessageData_ofFormat(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2));
v___x_953_ = l_Lean_MessageData_ofFormat(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
if (lean_obj_tag(v_x_955_) == 0)
{
return v_x_954_;
}
else
{
lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_979_; 
v_head_956_ = lean_ctor_get(v_x_955_, 0);
v_tail_957_ = lean_ctor_get(v_x_955_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_x_955_);
if (v_isSharedCheck_979_ == 0)
{
v___x_959_ = v_x_955_;
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tail_957_);
lean_inc(v_head_956_);
lean_dec(v_x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_before_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_977_; 
v_before_961_ = lean_ctor_get(v_head_956_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v_head_956_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_head_956_, 1);
lean_dec(v_unused_978_);
v___x_963_ = v_head_956_;
v_isShared_964_ = v_isSharedCheck_977_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_before_961_);
lean_dec(v_head_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_977_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 7);
lean_ctor_set(v___x_963_, 1, v___x_965_);
lean_ctor_set(v___x_963_, 0, v_x_954_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_x_954_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_976_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 7);
lean_ctor_set(v___x_959_, 1, v___x_968_);
lean_ctor_set(v___x_959_, 0, v___x_967_);
v___x_970_ = v___x_959_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_975_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = l_Lean_MessageData_ofSyntax(v_before_961_);
v___x_972_ = l_Lean_indentD(v___x_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v_x_954_ = v___x_973_;
v_x_955_ = v_tail_957_;
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
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_984_ = l_Lean_MessageData_ofFormat(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_985_, lean_object* v_macroStack_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_options_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_options_989_ = lean_ctor_get(v___y_987_, 1);
v___x_990_ = l_Lean_Elab_pp_macroStack;
v___x_991_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v_macroStack_986_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_msgData_985_);
return v___x_992_;
}
else
{
if (lean_obj_tag(v_macroStack_986_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_msgData_985_);
return v___x_993_;
}
else
{
lean_object* v_head_994_; lean_object* v_after_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1010_; 
v_head_994_ = lean_ctor_get(v_macroStack_986_, 0);
lean_inc(v_head_994_);
v_after_995_ = lean_ctor_get(v_head_994_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_head_994_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_head_994_, 0);
lean_dec(v_unused_1011_);
v___x_997_ = v_head_994_;
v_isShared_998_ = v_isSharedCheck_1010_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_after_995_);
lean_dec(v_head_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1010_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 7);
lean_ctor_set(v___x_997_, 1, v___x_999_);
lean_ctor_set(v___x_997_, 0, v_msgData_985_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_msgData_985_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_msgData_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1002_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_MessageData_ofSyntax(v_after_995_);
v___x_1005_ = l_Lean_indentD(v___x_1004_);
v_msgData_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1006_, 0, v___x_1003_);
lean_ctor_set(v_msgData_1006_, 1, v___x_1005_);
v___x_1007_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_msgData_1006_, v_macroStack_986_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1012_, lean_object* v_macroStack_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1012_, v_macroStack_1013_, v___y_1014_);
lean_dec_ref(v___y_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_ref_1025_; lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v_macroStack_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_ref_1025_ = lean_ctor_get(v___y_1022_, 4);
v___x_1026_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1017_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v_macroStack_1028_ = lean_ctor_get(v___y_1018_, 1);
v___x_1029_ = l_Lean_Elab_getBetterRef(v_ref_1025_, v_macroStack_1028_);
lean_inc(v_macroStack_1028_);
v___x_1030_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_1027_, v_macroStack_1028_, v___y_1022_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1029_);
lean_ctor_set(v___x_1035_, 1, v_a_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Lean_Elab_abortTermExceptionId;
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_1061_ = l_Lean_MessageData_ofExpr(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_1063_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_1069_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_ty_x3f_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_toCold_1091_; lean_object* v_options_1092_; lean_object* v_currRecDepth_1093_; lean_object* v_maxRecDepth_1094_; lean_object* v_ref_1095_; lean_object* v_currNamespace_1096_; lean_object* v_openDecls_1097_; lean_object* v_initHeartbeats_1098_; lean_object* v_maxHeartbeats_1099_; lean_object* v_currMacroScope_1100_; uint8_t v_diag_1101_; uint8_t v_suppressElabErrors_1102_; uint8_t v___x_1103_; lean_object* v_ref_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_ty_x3f_1085_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_1086_ = 1;
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_box(v___x_1086_);
v___x_1089_ = lean_box(v___x_1086_);
lean_inc(v_stx_1077_);
v___x_1090_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1090_, 0, v_stx_1077_);
lean_closure_set(v___x_1090_, 1, v_ty_x3f_1085_);
lean_closure_set(v___x_1090_, 2, v___x_1088_);
lean_closure_set(v___x_1090_, 3, v___x_1089_);
lean_closure_set(v___x_1090_, 4, v___x_1087_);
v_toCold_1091_ = lean_ctor_get(v_a_1082_, 0);
v_options_1092_ = lean_ctor_get(v_a_1082_, 1);
v_currRecDepth_1093_ = lean_ctor_get(v_a_1082_, 2);
v_maxRecDepth_1094_ = lean_ctor_get(v_a_1082_, 3);
v_ref_1095_ = lean_ctor_get(v_a_1082_, 4);
v_currNamespace_1096_ = lean_ctor_get(v_a_1082_, 5);
v_openDecls_1097_ = lean_ctor_get(v_a_1082_, 6);
v_initHeartbeats_1098_ = lean_ctor_get(v_a_1082_, 7);
v_maxHeartbeats_1099_ = lean_ctor_get(v_a_1082_, 8);
v_currMacroScope_1100_ = lean_ctor_get(v_a_1082_, 9);
v_diag_1101_ = lean_ctor_get_uint8(v_a_1082_, sizeof(void*)*10);
v_suppressElabErrors_1102_ = lean_ctor_get_uint8(v_a_1082_, sizeof(void*)*10 + 1);
v___x_1103_ = 1;
v_ref_1104_ = l_Lean_replaceRef(v_stx_1077_, v_ref_1095_);
lean_dec(v_stx_1077_);
lean_inc(v_currMacroScope_1100_);
lean_inc(v_maxHeartbeats_1099_);
lean_inc(v_initHeartbeats_1098_);
lean_inc(v_openDecls_1097_);
lean_inc(v_currNamespace_1096_);
lean_inc(v_maxRecDepth_1094_);
lean_inc(v_currRecDepth_1093_);
lean_inc_ref(v_options_1092_);
lean_inc_ref(v_toCold_1091_);
v___x_1105_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1105_, 0, v_toCold_1091_);
lean_ctor_set(v___x_1105_, 1, v_options_1092_);
lean_ctor_set(v___x_1105_, 2, v_currRecDepth_1093_);
lean_ctor_set(v___x_1105_, 3, v_maxRecDepth_1094_);
lean_ctor_set(v___x_1105_, 4, v_ref_1104_);
lean_ctor_set(v___x_1105_, 5, v_currNamespace_1096_);
lean_ctor_set(v___x_1105_, 6, v_openDecls_1097_);
lean_ctor_set(v___x_1105_, 7, v_initHeartbeats_1098_);
lean_ctor_set(v___x_1105_, 8, v_maxHeartbeats_1099_);
lean_ctor_set(v___x_1105_, 9, v_currMacroScope_1100_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*10, v_diag_1101_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*10 + 1, v_suppressElabErrors_1102_);
v___x_1106_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1090_, v___x_1103_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v___x_1105_, v_a_1083_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___x_1204_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_1107_, v_a_1081_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
v___x_1204_ = l_Lean_Expr_hasSorry(v_a_1109_);
if (v___x_1204_ == 0)
{
v___y_1149_ = v_a_1078_;
v___y_1150_ = v_a_1079_;
v___y_1151_ = v_a_1080_;
v___y_1152_ = v_a_1081_;
v___y_1153_ = v___x_1105_;
v___y_1154_ = v_a_1083_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_Expr_hasSyntheticSorry(v_a_1109_);
if (v___x_1205_ == 0)
{
v___y_1186_ = v_a_1078_;
v___y_1187_ = v_a_1079_;
v___y_1188_ = v_a_1080_;
v___y_1189_ = v_a_1081_;
v___y_1190_ = v___x_1105_;
v___y_1191_ = v_a_1083_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1109_);
lean_dec_ref_known(v___x_1105_, 10);
v___x_1206_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
v___jp_1110_:
{
if (v___y_1120_ == 0)
{
if (lean_obj_tag(v___y_1119_) == 0)
{
lean_dec_ref_known(v___y_1119_, 2);
lean_dec_ref(v___y_1114_);
lean_dec(v_a_1109_);
return v___y_1115_;
}
else
{
lean_object* v_id_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1134_; 
v_id_1121_ = lean_ctor_get(v___y_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___y_1119_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___y_1119_, 1);
lean_dec(v_unused_1135_);
v___x_1123_ = v___y_1119_;
v_isShared_1124_ = v_isSharedCheck_1134_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_id_1121_);
lean_dec(v___y_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1134_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1112_, v_id_1121_);
lean_dec(v_id_1121_);
if (v___x_1125_ == 0)
{
lean_del_object(v___x_1123_);
lean_dec_ref(v___y_1114_);
lean_dec(v_a_1109_);
return v___y_1115_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec_ref(v___y_1115_);
v___x_1126_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6);
v___x_1127_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_1128_ = l_Lean_indentExpr(v_a_1109_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 7);
lean_ctor_set(v___x_1123_, 1, v___x_1128_);
lean_ctor_set(v___x_1123_, 0, v___x_1127_);
v___x_1130_ = v___x_1123_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1126_);
v___x_1132_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1131_, v___y_1116_, v___y_1111_, v___y_1117_, v___y_1118_, v___y_1114_, v___y_1113_);
lean_dec_ref(v___y_1114_);
return v___x_1132_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1119_);
lean_dec_ref(v___y_1114_);
lean_dec(v_a_1109_);
return v___y_1115_;
}
}
v___jp_1136_:
{
lean_object* v___x_1143_; 
lean_inc(v_a_1109_);
v___x_1143_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_1109_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_dec_ref(v___y_1141_);
lean_dec(v_a_1109_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
v___x_1145_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1146_ = l_Lean_Exception_isInterrupt(v_a_1144_);
if (v___x_1146_ == 0)
{
uint8_t v___x_1147_; 
lean_inc(v_a_1144_);
v___x_1147_ = l_Lean_Exception_isRuntime(v_a_1144_);
v___y_1111_ = v___y_1138_;
v___y_1112_ = v___x_1145_;
v___y_1113_ = v___y_1142_;
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___x_1143_;
v___y_1116_ = v___y_1137_;
v___y_1117_ = v___y_1139_;
v___y_1118_ = v___y_1140_;
v___y_1119_ = v_a_1144_;
v___y_1120_ = v___x_1147_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v___y_1138_;
v___y_1112_ = v___x_1145_;
v___y_1113_ = v___y_1142_;
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___x_1143_;
v___y_1116_ = v___y_1137_;
v___y_1117_ = v___y_1139_;
v___y_1118_ = v___y_1140_;
v___y_1119_ = v_a_1144_;
v___y_1120_ = v___x_1146_;
goto v___jp_1110_;
}
}
}
v___jp_1148_:
{
lean_object* v___x_1155_; 
lean_inc(v_a_1109_);
v___x_1155_ = l_Lean_Meta_getMVars(v_a_1109_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1156_, v___x_1087_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v_a_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; uint8_t v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1159_ == 0)
{
v___y_1137_ = v___y_1149_;
v___y_1138_ = v___y_1150_;
v___y_1139_ = v___y_1151_;
v___y_1140_ = v___y_1152_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1109_);
v___x_1160_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1109_);
v_a_1169_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1157_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1157_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1109_);
v_a_1177_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1155_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1155_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
v___jp_1185_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v___x_1192_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_1193_ = l_Lean_indentExpr(v_a_1109_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1194_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec_ref(v___y_1190_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref_known(v___x_1105_, 10);
v_a_1215_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1106_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1106_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_stx_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(lean_object* v_config_1301_, lean_object* v_item_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_item_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1321_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1302_, v___x_1320_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1321_) == 0)
{
uint8_t v___x_1322_; 
lean_dec_ref_known(v___x_1321_, 1);
v___x_1322_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1302_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1323_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1302_);
lean_inc_ref(v_item_1302_);
v___x_1324_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1302_);
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_1326_ = lean_string_dec_lt(v___x_1323_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_1328_ = lean_string_dec_lt(v___x_1323_, v___x_1327_);
if (v___x_1328_ == 0)
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_string_dec_eq(v___x_1323_, v___x_1327_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_1331_ = lean_string_dec_eq(v___x_1323_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_1333_ = lean_string_dec_eq(v___x_1323_, v___x_1332_);
lean_dec_ref(v___x_1323_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_1335_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1334_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1335_) == 0)
{
uint8_t v___x_1336_; 
lean_dec_ref_known(v___x_1335_, 1);
v___x_1336_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1337_; 
lean_dec_ref(v___x_1324_);
v___x_1337_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1363_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1363_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1363_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v_proofs_1342_; uint8_t v_types_1343_; uint8_t v_implicits_1344_; uint8_t v_descend_1345_; uint8_t v_underBinder_1346_; uint8_t v_merge_1347_; uint8_t v_useContext_1348_; uint8_t v_onlyGivenNames_1349_; uint8_t v_preserveBinderNames_1350_; uint8_t v_lift_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
v_proofs_1342_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1343_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1344_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1345_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1346_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_merge_1347_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1348_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1349_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1350_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1351_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1353_ = v_config_1301_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v_config_1301_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, 0, v_proofs_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, 1, v_types_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, 2, v_implicits_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, 3, v_descend_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, 4, v_underBinder_1346_);
v___x_1356_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
uint8_t v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_unbox(v_a_1338_);
lean_dec(v_a_1338_);
lean_ctor_set_uint8(v___x_1356_, 5, v___x_1357_);
lean_ctor_set_uint8(v___x_1356_, 6, v_merge_1347_);
lean_ctor_set_uint8(v___x_1356_, 7, v_useContext_1348_);
lean_ctor_set_uint8(v___x_1356_, 8, v_onlyGivenNames_1349_);
lean_ctor_set_uint8(v___x_1356_, 9, v_preserveBinderNames_1350_);
lean_ctor_set_uint8(v___x_1356_, 10, v_lift_1351_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1356_);
v___x_1359_ = v___x_1340_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1356_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_config_1301_);
v_a_1364_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1337_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1337_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1372_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1335_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1335_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
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
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v___x_1323_);
v___x_1380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_1381_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1380_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1381_) == 0)
{
uint8_t v___x_1382_; 
lean_dec_ref_known(v___x_1381_, 1);
v___x_1382_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v___x_1324_);
v___x_1383_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1409_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1409_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1409_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v_proofs_1388_; uint8_t v_types_1389_; uint8_t v_implicits_1390_; uint8_t v_descend_1391_; uint8_t v_underBinder_1392_; uint8_t v_usedOnly_1393_; uint8_t v_merge_1394_; uint8_t v_onlyGivenNames_1395_; uint8_t v_preserveBinderNames_1396_; uint8_t v_lift_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v_proofs_1388_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1389_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1390_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1391_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1392_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1393_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1394_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_onlyGivenNames_1395_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1396_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1397_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1399_ = v_config_1301_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_config_1301_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 0, v_proofs_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 1, v_types_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 2, v_implicits_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 3, v_descend_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 4, v_underBinder_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 5, v_usedOnly_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, 6, v_merge_1394_);
v___x_1402_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
uint8_t v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_unbox(v_a_1384_);
lean_dec(v_a_1384_);
lean_ctor_set_uint8(v___x_1402_, 7, v___x_1403_);
lean_ctor_set_uint8(v___x_1402_, 8, v_onlyGivenNames_1395_);
lean_ctor_set_uint8(v___x_1402_, 9, v_preserveBinderNames_1396_);
lean_ctor_set_uint8(v___x_1402_, 10, v_lift_1397_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1402_);
v___x_1405_ = v___x_1386_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1402_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v_config_1301_);
v_a_1410_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1383_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1383_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1418_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1381_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1381_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
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
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___x_1323_);
v___x_1426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_1427_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1426_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1427_) == 0)
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v___x_1427_, 1);
v___x_1428_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1429_; 
lean_dec_ref(v___x_1324_);
v___x_1429_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1455_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1455_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1455_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v_proofs_1434_; uint8_t v_types_1435_; uint8_t v_implicits_1436_; uint8_t v_descend_1437_; uint8_t v_usedOnly_1438_; uint8_t v_merge_1439_; uint8_t v_useContext_1440_; uint8_t v_onlyGivenNames_1441_; uint8_t v_preserveBinderNames_1442_; uint8_t v_lift_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1454_; 
v_proofs_1434_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1435_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1436_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1437_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_usedOnly_1438_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1439_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1440_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1441_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1442_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1443_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1445_ = v_config_1301_;
v_isShared_1446_ = v_isSharedCheck_1454_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_config_1301_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1454_;
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
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1453_, 0, v_proofs_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1453_, 1, v_types_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1453_, 2, v_implicits_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1453_, 3, v_descend_1437_);
v___x_1448_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
uint8_t v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unbox(v_a_1430_);
lean_dec(v_a_1430_);
lean_ctor_set_uint8(v___x_1448_, 4, v___x_1449_);
lean_ctor_set_uint8(v___x_1448_, 5, v_usedOnly_1438_);
lean_ctor_set_uint8(v___x_1448_, 6, v_merge_1439_);
lean_ctor_set_uint8(v___x_1448_, 7, v_useContext_1440_);
lean_ctor_set_uint8(v___x_1448_, 8, v_onlyGivenNames_1441_);
lean_ctor_set_uint8(v___x_1448_, 9, v_preserveBinderNames_1442_);
lean_ctor_set_uint8(v___x_1448_, 10, v_lift_1443_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1448_);
v___x_1451_ = v___x_1432_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v_config_1301_);
v_a_1456_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1429_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1429_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1464_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1427_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1427_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_string_dec_eq(v___x_1323_, v___x_1325_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_1474_ = lean_string_dec_eq(v___x_1323_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_1476_ = lean_string_dec_eq(v___x_1323_, v___x_1475_);
lean_dec_ref(v___x_1323_);
if (v___x_1476_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_1478_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1477_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1478_) == 0)
{
uint8_t v___x_1479_; 
lean_dec_ref_known(v___x_1478_, 1);
v___x_1479_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1479_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1480_; 
lean_dec_ref(v___x_1324_);
v___x_1480_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1506_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint8_t v_proofs_1485_; uint8_t v_implicits_1486_; uint8_t v_descend_1487_; uint8_t v_underBinder_1488_; uint8_t v_usedOnly_1489_; uint8_t v_merge_1490_; uint8_t v_useContext_1491_; uint8_t v_onlyGivenNames_1492_; uint8_t v_preserveBinderNames_1493_; uint8_t v_lift_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1505_; 
v_proofs_1485_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_implicits_1486_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1487_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1488_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1489_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1490_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1491_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1492_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1493_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1494_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1496_ = v_config_1301_;
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v_config_1301_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, 0, v_proofs_1485_);
v___x_1499_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
uint8_t v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_unbox(v_a_1481_);
lean_dec(v_a_1481_);
lean_ctor_set_uint8(v___x_1499_, 1, v___x_1500_);
lean_ctor_set_uint8(v___x_1499_, 2, v_implicits_1486_);
lean_ctor_set_uint8(v___x_1499_, 3, v_descend_1487_);
lean_ctor_set_uint8(v___x_1499_, 4, v_underBinder_1488_);
lean_ctor_set_uint8(v___x_1499_, 5, v_usedOnly_1489_);
lean_ctor_set_uint8(v___x_1499_, 6, v_merge_1490_);
lean_ctor_set_uint8(v___x_1499_, 7, v_useContext_1491_);
lean_ctor_set_uint8(v___x_1499_, 8, v_onlyGivenNames_1492_);
lean_ctor_set_uint8(v___x_1499_, 9, v_preserveBinderNames_1493_);
lean_ctor_set_uint8(v___x_1499_, 10, v_lift_1494_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1499_);
v___x_1502_ = v___x_1483_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1499_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_config_1301_);
v_a_1507_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1480_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1480_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1515_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1478_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1478_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
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
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref(v___x_1323_);
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_1524_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1523_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1524_) == 0)
{
uint8_t v___x_1525_; 
lean_dec_ref_known(v___x_1524_, 1);
v___x_1525_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v___x_1324_);
v___x_1526_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1552_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1552_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1552_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
uint8_t v_types_1531_; uint8_t v_implicits_1532_; uint8_t v_descend_1533_; uint8_t v_underBinder_1534_; uint8_t v_usedOnly_1535_; uint8_t v_merge_1536_; uint8_t v_useContext_1537_; uint8_t v_onlyGivenNames_1538_; uint8_t v_preserveBinderNames_1539_; uint8_t v_lift_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1551_; 
v_types_1531_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1532_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1533_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1534_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1535_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1536_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1537_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1538_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1539_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1540_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1542_ = v_config_1301_;
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v_config_1301_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 0, 11);
v___x_1545_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
uint8_t v___x_1546_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unbox(v_a_1527_);
lean_dec(v_a_1527_);
lean_ctor_set_uint8(v___x_1545_, 0, v___x_1546_);
lean_ctor_set_uint8(v___x_1545_, 1, v_types_1531_);
lean_ctor_set_uint8(v___x_1545_, 2, v_implicits_1532_);
lean_ctor_set_uint8(v___x_1545_, 3, v_descend_1533_);
lean_ctor_set_uint8(v___x_1545_, 4, v_underBinder_1534_);
lean_ctor_set_uint8(v___x_1545_, 5, v_usedOnly_1535_);
lean_ctor_set_uint8(v___x_1545_, 6, v_merge_1536_);
lean_ctor_set_uint8(v___x_1545_, 7, v_useContext_1537_);
lean_ctor_set_uint8(v___x_1545_, 8, v_onlyGivenNames_1538_);
lean_ctor_set_uint8(v___x_1545_, 9, v_preserveBinderNames_1539_);
lean_ctor_set_uint8(v___x_1545_, 10, v_lift_1540_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1545_);
v___x_1548_ = v___x_1529_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1545_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_config_1301_);
v_a_1553_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1526_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1526_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
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
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1561_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1524_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1524_);
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
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v___x_1323_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_1570_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1569_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1570_) == 0)
{
uint8_t v___x_1571_; 
lean_dec_ref_known(v___x_1570_, 1);
v___x_1571_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1571_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1572_; 
lean_dec_ref(v___x_1324_);
v___x_1572_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1598_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1598_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1598_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint8_t v_proofs_1577_; uint8_t v_types_1578_; uint8_t v_implicits_1579_; uint8_t v_descend_1580_; uint8_t v_underBinder_1581_; uint8_t v_usedOnly_1582_; uint8_t v_merge_1583_; uint8_t v_useContext_1584_; uint8_t v_onlyGivenNames_1585_; uint8_t v_lift_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1597_; 
v_proofs_1577_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1578_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1579_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1580_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1581_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1582_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1583_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1584_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1585_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_lift_1586_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1588_ = v_config_1301_;
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
else
{
lean_dec(v_config_1301_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 0, v_proofs_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 1, v_types_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 2, v_implicits_1579_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 3, v_descend_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 4, v_underBinder_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 5, v_usedOnly_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 6, v_merge_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 7, v_useContext_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, 8, v_onlyGivenNames_1585_);
v___x_1591_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
uint8_t v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
lean_ctor_set_uint8(v___x_1591_, 9, v___x_1592_);
lean_ctor_set_uint8(v___x_1591_, 10, v_lift_1586_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1591_);
v___x_1594_ = v___x_1575_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1591_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v_config_1301_);
v_a_1599_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1572_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1572_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1607_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1570_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1570_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_1616_ = lean_string_dec_lt(v___x_1323_, v___x_1615_);
if (v___x_1616_ == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_string_dec_eq(v___x_1323_, v___x_1615_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_1619_ = lean_string_dec_eq(v___x_1323_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_1621_ = lean_string_dec_eq(v___x_1323_, v___x_1620_);
lean_dec_ref(v___x_1323_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_1623_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1622_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1623_) == 0)
{
uint8_t v___x_1624_; 
lean_dec_ref_known(v___x_1623_, 1);
v___x_1624_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1624_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1625_; 
lean_dec_ref(v___x_1324_);
v___x_1625_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1651_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
uint8_t v_proofs_1630_; uint8_t v_types_1631_; uint8_t v_implicits_1632_; uint8_t v_descend_1633_; uint8_t v_underBinder_1634_; uint8_t v_usedOnly_1635_; uint8_t v_merge_1636_; uint8_t v_useContext_1637_; uint8_t v_preserveBinderNames_1638_; uint8_t v_lift_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1650_; 
v_proofs_1630_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1631_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1632_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1633_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1634_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1635_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1636_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1637_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_preserveBinderNames_1638_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1639_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1641_ = v_config_1301_;
v_isShared_1642_ = v_isSharedCheck_1650_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_config_1301_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1650_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 0, v_proofs_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 1, v_types_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 2, v_implicits_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 3, v_descend_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 4, v_underBinder_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 5, v_usedOnly_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 6, v_merge_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, 7, v_useContext_1637_);
v___x_1644_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
uint8_t v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unbox(v_a_1626_);
lean_dec(v_a_1626_);
lean_ctor_set_uint8(v___x_1644_, 8, v___x_1645_);
lean_ctor_set_uint8(v___x_1644_, 9, v_preserveBinderNames_1638_);
lean_ctor_set_uint8(v___x_1644_, 10, v_lift_1639_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1644_);
v___x_1647_ = v___x_1628_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1644_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_config_1301_);
v_a_1652_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1625_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1625_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1660_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1623_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1623_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
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
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1323_);
v___x_1668_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_1669_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1668_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1669_) == 0)
{
uint8_t v___x_1670_; 
lean_dec_ref_known(v___x_1669_, 1);
v___x_1670_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1670_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1671_; 
lean_dec_ref(v___x_1324_);
v___x_1671_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1697_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1697_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1697_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
uint8_t v_proofs_1676_; uint8_t v_types_1677_; uint8_t v_implicits_1678_; uint8_t v_descend_1679_; uint8_t v_underBinder_1680_; uint8_t v_usedOnly_1681_; uint8_t v_useContext_1682_; uint8_t v_onlyGivenNames_1683_; uint8_t v_preserveBinderNames_1684_; uint8_t v_lift_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1696_; 
v_proofs_1676_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1677_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1678_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1679_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1680_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1681_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_useContext_1682_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1683_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1684_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1685_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1687_ = v_config_1301_;
v_isShared_1688_ = v_isSharedCheck_1696_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v_config_1301_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1696_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 0, v_proofs_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 1, v_types_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 2, v_implicits_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 3, v_descend_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 4, v_underBinder_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, 5, v_usedOnly_1681_);
v___x_1690_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
uint8_t v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_unbox(v_a_1672_);
lean_dec(v_a_1672_);
lean_ctor_set_uint8(v___x_1690_, 6, v___x_1691_);
lean_ctor_set_uint8(v___x_1690_, 7, v_useContext_1682_);
lean_ctor_set_uint8(v___x_1690_, 8, v_onlyGivenNames_1683_);
lean_ctor_set_uint8(v___x_1690_, 9, v_preserveBinderNames_1684_);
lean_ctor_set_uint8(v___x_1690_, 10, v_lift_1685_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1690_);
v___x_1693_ = v___x_1674_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_config_1301_);
v_a_1698_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1671_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1671_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1706_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1669_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1669_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
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
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v___x_1323_);
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_1715_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1714_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1715_) == 0)
{
uint8_t v___x_1716_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1716_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1324_);
v___x_1717_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1743_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1743_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1743_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
uint8_t v_proofs_1722_; uint8_t v_types_1723_; uint8_t v_implicits_1724_; uint8_t v_descend_1725_; uint8_t v_underBinder_1726_; uint8_t v_usedOnly_1727_; uint8_t v_merge_1728_; uint8_t v_useContext_1729_; uint8_t v_onlyGivenNames_1730_; uint8_t v_preserveBinderNames_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1742_; 
v_proofs_1722_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1723_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1724_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_descend_1725_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1726_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1727_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1728_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1729_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1730_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1731_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1733_ = v_config_1301_;
v_isShared_1734_ = v_isSharedCheck_1742_;
goto v_resetjp_1732_;
}
else
{
lean_dec(v_config_1301_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1742_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 0, v_proofs_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 1, v_types_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 2, v_implicits_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 3, v_descend_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 4, v_underBinder_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 5, v_usedOnly_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 6, v_merge_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 7, v_useContext_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 8, v_onlyGivenNames_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, 9, v_preserveBinderNames_1731_);
v___x_1736_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
uint8_t v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = lean_unbox(v_a_1718_);
lean_dec(v_a_1718_);
lean_ctor_set_uint8(v___x_1736_, 10, v___x_1737_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1736_);
v___x_1739_ = v___x_1720_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1736_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v_config_1301_);
v_a_1744_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1717_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1717_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1752_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1715_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1715_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
else
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_1761_ = lean_string_dec_eq(v___x_1323_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_1763_ = lean_string_dec_eq(v___x_1323_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_1765_ = lean_string_dec_eq(v___x_1323_, v___x_1764_);
lean_dec_ref(v___x_1323_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_1767_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1766_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1767_) == 0)
{
uint8_t v___x_1768_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1769_; 
lean_dec_ref(v___x_1324_);
v___x_1769_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1795_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1795_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1795_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v_proofs_1774_; uint8_t v_types_1775_; uint8_t v_descend_1776_; uint8_t v_underBinder_1777_; uint8_t v_usedOnly_1778_; uint8_t v_merge_1779_; uint8_t v_useContext_1780_; uint8_t v_onlyGivenNames_1781_; uint8_t v_preserveBinderNames_1782_; uint8_t v_lift_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1794_; 
v_proofs_1774_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1775_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_descend_1776_ = lean_ctor_get_uint8(v_config_1301_, 3);
v_underBinder_1777_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1778_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1779_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1780_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1781_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1782_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1783_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1785_ = v_config_1301_;
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
else
{
lean_dec(v_config_1301_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, 0, v_proofs_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, 1, v_types_1775_);
v___x_1788_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
uint8_t v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_unbox(v_a_1770_);
lean_dec(v_a_1770_);
lean_ctor_set_uint8(v___x_1788_, 2, v___x_1789_);
lean_ctor_set_uint8(v___x_1788_, 3, v_descend_1776_);
lean_ctor_set_uint8(v___x_1788_, 4, v_underBinder_1777_);
lean_ctor_set_uint8(v___x_1788_, 5, v_usedOnly_1778_);
lean_ctor_set_uint8(v___x_1788_, 6, v_merge_1779_);
lean_ctor_set_uint8(v___x_1788_, 7, v_useContext_1780_);
lean_ctor_set_uint8(v___x_1788_, 8, v_onlyGivenNames_1781_);
lean_ctor_set_uint8(v___x_1788_, 9, v_preserveBinderNames_1782_);
lean_ctor_set_uint8(v___x_1788_, 10, v_lift_1783_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1788_);
v___x_1791_ = v___x_1772_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1788_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_config_1301_);
v_a_1796_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1769_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1769_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1804_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1767_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1767_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
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
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v___x_1323_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_1813_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1302_, v___x_1812_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1813_) == 0)
{
uint8_t v___x_1814_; 
lean_dec_ref_known(v___x_1813_, 1);
v___x_1814_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1815_; 
lean_dec_ref(v___x_1324_);
v___x_1815_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1841_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1841_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1841_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v_proofs_1820_; uint8_t v_types_1821_; uint8_t v_implicits_1822_; uint8_t v_underBinder_1823_; uint8_t v_usedOnly_1824_; uint8_t v_merge_1825_; uint8_t v_useContext_1826_; uint8_t v_onlyGivenNames_1827_; uint8_t v_preserveBinderNames_1828_; uint8_t v_lift_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1840_; 
v_proofs_1820_ = lean_ctor_get_uint8(v_config_1301_, 0);
v_types_1821_ = lean_ctor_get_uint8(v_config_1301_, 1);
v_implicits_1822_ = lean_ctor_get_uint8(v_config_1301_, 2);
v_underBinder_1823_ = lean_ctor_get_uint8(v_config_1301_, 4);
v_usedOnly_1824_ = lean_ctor_get_uint8(v_config_1301_, 5);
v_merge_1825_ = lean_ctor_get_uint8(v_config_1301_, 6);
v_useContext_1826_ = lean_ctor_get_uint8(v_config_1301_, 7);
v_onlyGivenNames_1827_ = lean_ctor_get_uint8(v_config_1301_, 8);
v_preserveBinderNames_1828_ = lean_ctor_get_uint8(v_config_1301_, 9);
v_lift_1829_ = lean_ctor_get_uint8(v_config_1301_, 10);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_config_1301_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1831_ = v_config_1301_;
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_config_1301_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, 0, v_proofs_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, 1, v_types_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, 2, v_implicits_1822_);
v___x_1834_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
uint8_t v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
lean_ctor_set_uint8(v___x_1834_, 3, v___x_1835_);
lean_ctor_set_uint8(v___x_1834_, 4, v_underBinder_1823_);
lean_ctor_set_uint8(v___x_1834_, 5, v_usedOnly_1824_);
lean_ctor_set_uint8(v___x_1834_, 6, v_merge_1825_);
lean_ctor_set_uint8(v___x_1834_, 7, v_useContext_1826_);
lean_ctor_set_uint8(v___x_1834_, 8, v_onlyGivenNames_1827_);
lean_ctor_set_uint8(v___x_1834_, 9, v_preserveBinderNames_1828_);
lean_ctor_set_uint8(v___x_1834_, 10, v_lift_1829_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1834_);
v___x_1837_ = v___x_1818_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_config_1301_);
v_a_1842_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1815_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1815_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1850_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1813_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1813_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
else
{
uint8_t v___x_1858_; 
lean_dec_ref(v___x_1323_);
lean_dec_ref(v_config_1301_);
v___x_1858_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1324_);
if (v___x_1858_ == 0)
{
lean_dec_ref(v_item_1302_);
v_item_1311_ = v___x_1324_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v_value_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v___x_1324_);
v_value_1859_ = lean_ctor_get(v_item_1302_, 2);
lean_inc(v_value_1859_);
lean_dec_ref(v_item_1302_);
v___x_1860_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_value_1859_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1860_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_1301_);
v_item_1311_ = v_item_1302_;
v___y_1312_ = v___y_1303_;
v___y_1313_ = v___y_1304_;
v___y_1314_ = v___y_1305_;
v___y_1315_ = v___y_1306_;
v___y_1316_ = v___y_1307_;
v___y_1317_ = v___y_1308_;
goto v___jp_1310_;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_item_1302_);
lean_dec_ref(v_config_1301_);
v_a_1861_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1321_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1321_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
v___jp_1310_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_1319_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1311_, v___x_1318_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1869_, lean_object* v_item_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(v_config_1869_, v_item_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1881_, v___y_1885_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(v_e_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1917_, lean_object* v_msg_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1927_, v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1937_, lean_object* v_macroStack_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1937_, v_macroStack_1938_, v___y_1943_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1947_, lean_object* v_macroStack_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1947_, v_macroStack_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1959_ = l_Lean_mkConst(v___x_1958_, v___x_1957_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(lean_object* v_cfg_1962_, lean_object* v_cfgItem_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1);
v___x_1972_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1962_, v_cfgItem_1963_, v___x_1971_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_1973_, lean_object* v_cfgItem_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(v_cfg_1973_, v_cfgItem_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_cfgItem_1974_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_cfg_1984_, lean_object* v_init_1985_, uint8_t v_logExceptions_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_onErr_1991_; lean_object* v_eval_1992_; 
v_onErr_1991_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v_eval_1992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_1986_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1992_, v_init_1985_, v_cfg_1984_, v_onErr_1991_, v_logExceptions_1986_, v_a_1988_, v_a_1989_);
return v___x_1993_;
}
else
{
uint8_t v_recover_1994_; lean_object* v___x_1995_; 
v_recover_1994_ = lean_ctor_get_uint8(v_a_1987_, sizeof(void*)*1);
v___x_1995_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1992_, v_init_1985_, v_cfg_1984_, v_onErr_1991_, v_recover_1994_, v_a_1988_, v_a_1989_);
return v___x_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_cfg_1996_, lean_object* v_init_1997_, lean_object* v_logExceptions_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
uint8_t v_logExceptions_boxed_2003_; lean_object* v_res_2004_; 
v_logExceptions_boxed_2003_ = lean_unbox(v_logExceptions_1998_);
v_res_2004_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_1996_, v_init_1997_, v_logExceptions_boxed_2003_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec_ref(v_a_1999_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_cfg_2005_, lean_object* v_init_2006_, uint8_t v_logExceptions_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_2005_, v_init_2006_, v_logExceptions_2007_, v_a_2008_, v_a_2014_, v_a_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_cfg_2018_, lean_object* v_init_2019_, lean_object* v_logExceptions_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
uint8_t v_logExceptions_boxed_2030_; lean_object* v_res_2031_; 
v_logExceptions_boxed_2030_ = lean_unbox(v_logExceptions_2020_);
v_res_2031_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_cfg_2018_, v_init_2019_, v_logExceptions_boxed_2030_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2031_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___closed__0);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_ref_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_ref_2068_ = lean_ctor_get(v___y_2065_, 4);
v___x_2069_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_inc(v_ref_2068_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ref_2068_);
lean_ctor_set(v___x_2074_, 1, v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set_tag(v___x_2072_, 1);
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2085_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_2100_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_2099_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v_x_2101_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_2112_, lean_object* v___x_2113_, lean_object* v_a_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2116_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_2125_, v_h_2112_, v___x_2113_, v_a_2114_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v_fst_2128_; lean_object* v_snd_2129_; lean_object* v_fst_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2155_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_fst_2128_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_fst_2128_);
v_snd_2129_ = lean_ctor_get(v_a_2127_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2127_);
v_fst_2130_ = lean_ctor_get(v_fst_2128_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_fst_2128_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_fst_2128_, 1);
lean_dec(v_unused_2156_);
v___x_2132_ = v_fst_2128_;
v_isShared_2133_ = v_isSharedCheck_2155_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_fst_2130_);
lean_dec(v_fst_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2155_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_box(0);
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 1);
lean_ctor_set(v___x_2132_, 1, v___x_2134_);
lean_ctor_set(v___x_2132_, 0, v_snd_2129_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_snd_2129_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2136_, v___y_2116_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2137_, 0);
lean_dec(v_unused_2145_);
v___x_2139_ = v___x_2137_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v___x_2137_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_fst_2130_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_fst_2130_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_fst_2130_);
v_a_2146_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2137_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2137_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
v_a_2157_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2126_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2126_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_a_2114_);
lean_dec(v___x_2113_);
lean_dec(v_h_2112_);
v_a_2165_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2124_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2124_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_2173_, lean_object* v___x_2174_, lean_object* v_a_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_2173_, v___x_2174_, v_a_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_2186_, lean_object* v_a_2187_, lean_object* v_ids_2188_, lean_object* v_h_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; 
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2199_, 0, v_h_2189_);
lean_closure_set(v___f_2199_, 1, v___x_2186_);
lean_closure_set(v___f_2199_, 2, v_a_2187_);
v___x_2200_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2199_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2188_, v_a_2201_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
return v___x_2202_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_ids_2188_);
v_a_2203_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2200_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2200_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_2211_, lean_object* v_a_2212_, lean_object* v_ids_2213_, lean_object* v_h_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_2211_, v_a_2212_, v_ids_2213_, v_h_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_2225_, lean_object* v_a_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2228_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l_Lean_MVarId_extractLets(v_a_2237_, v___x_2225_, v_a_2226_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v_fst_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2267_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v_fst_2240_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_fst_2240_);
v_snd_2241_ = lean_ctor_get(v_a_2239_, 1);
lean_inc(v_snd_2241_);
lean_dec(v_a_2239_);
v_fst_2242_ = lean_ctor_get(v_fst_2240_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_fst_2240_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v_fst_2240_, 1);
lean_dec(v_unused_2268_);
v___x_2244_ = v_fst_2240_;
v_isShared_2245_ = v_isSharedCheck_2267_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_fst_2242_);
lean_dec(v_fst_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2267_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_box(0);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 1);
lean_ctor_set(v___x_2244_, 1, v___x_2246_);
lean_ctor_set(v___x_2244_, 0, v_snd_2241_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_snd_2241_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2248_, v___y_2228_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2256_ == 0)
{
lean_object* v_unused_2257_; 
v_unused_2257_ = lean_ctor_get(v___x_2249_, 0);
lean_dec(v_unused_2257_);
v___x_2251_ = v___x_2249_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_dec(v___x_2249_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v_fst_2242_);
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_fst_2242_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_fst_2242_);
v_a_2258_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2249_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2249_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_a_2269_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2238_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2238_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_a_2226_);
lean_dec(v___x_2225_);
v_a_2277_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2236_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2236_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_2285_, lean_object* v_a_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_2285_, v_a_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_2297_, lean_object* v_ids_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2297_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2298_, v_a_2309_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2310_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_ids_2298_);
v_a_2311_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2308_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2308_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_2319_, lean_object* v_ids_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_2319_, v_ids_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_2331_, size_t v_i_2332_, lean_object* v_bs_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_lt(v_i_2332_, v_sz_2331_);
if (v___x_2334_ == 0)
{
return v_bs_2333_;
}
else
{
lean_object* v_v_2335_; lean_object* v___x_2336_; lean_object* v_bs_x27_2337_; lean_object* v___x_2338_; size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v_v_2335_ = lean_array_uget(v_bs_2333_, v_i_2332_);
v___x_2336_ = lean_unsigned_to_nat(0u);
v_bs_x27_2337_ = lean_array_uset(v_bs_2333_, v_i_2332_, v___x_2336_);
v___x_2338_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_2335_);
lean_dec(v_v_2335_);
v___x_2339_ = ((size_t)1ULL);
v___x_2340_ = lean_usize_add(v_i_2332_, v___x_2339_);
v___x_2341_ = lean_array_uset(v_bs_x27_2337_, v_i_2332_, v___x_2338_);
v_i_2332_ = v___x_2340_;
v_bs_2333_ = v___x_2341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_2343_, lean_object* v_i_2344_, lean_object* v_bs_2345_){
_start:
{
size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2343_);
lean_dec(v_sz_2343_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2344_);
lean_dec(v_i_2344_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_2346_, v_i_boxed_2347_, v_bs_2345_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_2369_);
v___x_2380_ = l_Lean_Syntax_isOfKind(v_x_2369_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v_x_2369_);
v___x_2381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2382_ = lean_unsigned_to_nat(1u);
v___x_2383_ = l_Lean_Syntax_getArg(v_x_2369_, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2383_);
v___x_2385_ = l_Lean_Syntax_isOfKind(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_dec(v___x_2383_);
lean_dec(v_x_2369_);
v___x_2386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2386_;
}
else
{
lean_object* v___f_2387_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v_loc_x3f_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___f_2387_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_2403_ = lean_unsigned_to_nat(2u);
v___x_2404_ = l_Lean_Syntax_getArg(v_x_2369_, v___x_2403_);
v___x_2444_ = lean_unsigned_to_nat(3u);
v___x_2445_ = l_Lean_Syntax_getArg(v_x_2369_, v___x_2444_);
lean_dec(v_x_2369_);
v___x_2446_ = l_Lean_Syntax_isNone(v___x_2445_);
if (v___x_2446_ == 0)
{
uint8_t v___x_2447_; 
lean_inc(v___x_2445_);
v___x_2447_ = l_Lean_Syntax_matchesNull(v___x_2445_, v___x_2382_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec(v___x_2445_);
lean_dec(v___x_2404_);
lean_dec(v___x_2383_);
v___x_2448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v_loc_x3f_2450_; 
v___x_2449_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2450_ = l_Lean_Syntax_getArg(v___x_2445_, v___x_2449_);
lean_dec(v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2450_);
v___x_2454_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2450_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec(v_loc_x3f_2450_);
lean_dec(v___x_2404_);
lean_dec(v___x_2383_);
v___x_2455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_2455_;
}
else
{
goto v___jp_2451_;
}
}
else
{
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_loc_x3f_2450_);
v_loc_x3f_2406_ = v___x_2452_;
v___y_2407_ = v_a_2370_;
v___y_2408_ = v_a_2371_;
v___y_2409_ = v_a_2372_;
v___y_2410_ = v_a_2373_;
v___y_2411_ = v_a_2374_;
v___y_2412_ = v_a_2375_;
v___y_2413_ = v_a_2376_;
v___y_2414_ = v_a_2377_;
goto v___jp_2405_;
}
}
}
else
{
lean_object* v___x_2456_; 
lean_dec(v___x_2445_);
v___x_2456_ = lean_box(0);
v_loc_x3f_2406_ = v___x_2456_;
v___y_2407_ = v_a_2370_;
v___y_2408_ = v_a_2371_;
v___y_2409_ = v_a_2372_;
v___y_2410_ = v_a_2373_;
v___y_2411_ = v_a_2374_;
v___y_2412_ = v_a_2375_;
v___y_2413_ = v_a_2376_;
v___y_2414_ = v_a_2377_;
goto v___jp_2405_;
}
v___jp_2388_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = l_Lean_mkOptionalNode(v___y_2399_);
v___x_2401_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2400_);
lean_dec(v___x_2400_);
v___x_2402_ = l_Lean_Elab_Tactic_withLocation(v___x_2401_, v___y_2396_, v___y_2398_, v___f_2387_, v___y_2390_, v___y_2397_, v___y_2389_, v___y_2391_, v___y_2393_, v___y_2392_, v___y_2395_, v___y_2394_);
lean_dec(v___x_2401_);
return v___x_2402_;
}
v___jp_2405_:
{
uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = 0;
v___x_2416_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2416_, 0, v___x_2415_);
lean_ctor_set_uint8(v___x_2416_, 1, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, 2, v___x_2415_);
lean_ctor_set_uint8(v___x_2416_, 3, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, 4, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, 5, v___x_2415_);
lean_ctor_set_uint8(v___x_2416_, 6, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, 7, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, 8, v___x_2415_);
lean_ctor_set_uint8(v___x_2416_, 9, v___x_2415_);
lean_ctor_set_uint8(v___x_2416_, 10, v___x_2415_);
v___x_2417_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_2383_, v___x_2416_, v___x_2385_, v___y_2407_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_ids_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___f_2426_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_n(v_a_2418_, 2);
lean_dec_ref_known(v___x_2417_, 1);
v_ids_2419_ = l_Lean_Syntax_getArgs(v___x_2404_);
lean_dec(v___x_2404_);
v_sz_2420_ = lean_array_size(v_ids_2419_);
v___x_2421_ = ((size_t)0ULL);
lean_inc_ref_n(v_ids_2419_, 2);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_2420_, v___x_2421_, v_ids_2419_);
v___x_2423_ = lean_array_to_list(v___x_2422_);
lean_inc(v___x_2423_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_2424_, 0, v___x_2423_);
lean_closure_set(v___f_2424_, 1, v_a_2418_);
lean_closure_set(v___f_2424_, 2, v_ids_2419_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2425_, 0, v___x_2423_);
lean_closure_set(v___f_2425_, 1, v_a_2418_);
v___f_2426_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_2426_, 0, v___f_2425_);
lean_closure_set(v___f_2426_, 1, v_ids_2419_);
if (lean_obj_tag(v_loc_x3f_2406_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_box(0);
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2410_;
v___y_2392_ = v___y_2412_;
v___y_2393_ = v___y_2411_;
v___y_2394_ = v___y_2414_;
v___y_2395_ = v___y_2413_;
v___y_2396_ = v___f_2424_;
v___y_2397_ = v___y_2408_;
v___y_2398_ = v___f_2426_;
v___y_2399_ = v___x_2427_;
goto v___jp_2388_;
}
else
{
lean_object* v_val_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_val_2428_ = lean_ctor_get(v_loc_x3f_2406_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_loc_x3f_2406_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v_loc_x3f_2406_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_val_2428_);
lean_dec(v_loc_x3f_2406_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_val_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2410_;
v___y_2392_ = v___y_2412_;
v___y_2393_ = v___y_2411_;
v___y_2394_ = v___y_2414_;
v___y_2395_ = v___y_2413_;
v___y_2396_ = v___f_2424_;
v___y_2397_ = v___y_2408_;
v___y_2398_ = v___f_2426_;
v___y_2399_ = v___x_2433_;
goto v___jp_2388_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_loc_x3f_2406_);
lean_dec(v___x_2404_);
v_a_2436_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2417_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2417_);
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
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_2468_, lean_object* v_msg_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v_msg_2469_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_2480_, lean_object* v_msg_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_2480_, v_msg_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2499_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2500_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_2501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_2502_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_2503_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2499_, v___x_2500_, v___x_2501_, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object* v___x_2506_, lean_object* v_ctor_2507_, lean_object* v_args_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_2535_ = lean_string_dec_eq(v_ctor_2507_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2537_ = lean_array_get_size(v_args_2508_);
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_nat_dec_eq(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_2541_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_2540_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
goto v___jp_2514_;
}
}
v___jp_2514_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_array_get_borrowed(v___x_2506_, v_args_2508_, v___x_2515_);
lean_inc(v___x_2516_);
v___x_2517_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v___x_2516_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object* v___x_2550_, lean_object* v_ctor_2551_, lean_object* v_args_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(v___x_2550_, v_ctor_2551_, v_args_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v_args_2552_);
lean_dec_ref(v_ctor_2551_);
lean_dec_ref(v___x_2550_);
return v_res_2558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___f_2560_; 
v___x_2559_ = l_Lean_instInhabitedExpr;
v___f_2560_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2560_, 0, v___x_2559_);
return v___f_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___f_2572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0);
v___x_2573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2574_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2573_, v___f_2572_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
return v_res_2581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_box(0);
v___x_2584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2585_ = l_Lean_Expr_const___override(v___x_2584_, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0));
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig(void){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2593_ = l_Lean_MessageData_ofExpr(v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_2598_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_ty_x3f_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_toCold_2614_; lean_object* v_options_2615_; lean_object* v_currRecDepth_2616_; lean_object* v_maxRecDepth_2617_; lean_object* v_ref_2618_; lean_object* v_currNamespace_2619_; lean_object* v_openDecls_2620_; lean_object* v_initHeartbeats_2621_; lean_object* v_maxHeartbeats_2622_; lean_object* v_currMacroScope_2623_; uint8_t v_diag_2624_; uint8_t v_suppressElabErrors_2625_; uint8_t v___x_2626_; lean_object* v_ref_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_ty_x3f_2608_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2609_ = 1;
v___x_2610_ = lean_box(0);
v___x_2611_ = lean_box(v___x_2609_);
v___x_2612_ = lean_box(v___x_2609_);
lean_inc(v_stx_2600_);
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2613_, 0, v_stx_2600_);
lean_closure_set(v___x_2613_, 1, v_ty_x3f_2608_);
lean_closure_set(v___x_2613_, 2, v___x_2611_);
lean_closure_set(v___x_2613_, 3, v___x_2612_);
lean_closure_set(v___x_2613_, 4, v___x_2610_);
v_toCold_2614_ = lean_ctor_get(v_a_2605_, 0);
v_options_2615_ = lean_ctor_get(v_a_2605_, 1);
v_currRecDepth_2616_ = lean_ctor_get(v_a_2605_, 2);
v_maxRecDepth_2617_ = lean_ctor_get(v_a_2605_, 3);
v_ref_2618_ = lean_ctor_get(v_a_2605_, 4);
v_currNamespace_2619_ = lean_ctor_get(v_a_2605_, 5);
v_openDecls_2620_ = lean_ctor_get(v_a_2605_, 6);
v_initHeartbeats_2621_ = lean_ctor_get(v_a_2605_, 7);
v_maxHeartbeats_2622_ = lean_ctor_get(v_a_2605_, 8);
v_currMacroScope_2623_ = lean_ctor_get(v_a_2605_, 9);
v_diag_2624_ = lean_ctor_get_uint8(v_a_2605_, sizeof(void*)*10);
v_suppressElabErrors_2625_ = lean_ctor_get_uint8(v_a_2605_, sizeof(void*)*10 + 1);
v___x_2626_ = 1;
v_ref_2627_ = l_Lean_replaceRef(v_stx_2600_, v_ref_2618_);
lean_dec(v_stx_2600_);
lean_inc(v_currMacroScope_2623_);
lean_inc(v_maxHeartbeats_2622_);
lean_inc(v_initHeartbeats_2621_);
lean_inc(v_openDecls_2620_);
lean_inc(v_currNamespace_2619_);
lean_inc(v_maxRecDepth_2617_);
lean_inc(v_currRecDepth_2616_);
lean_inc_ref(v_options_2615_);
lean_inc_ref(v_toCold_2614_);
v___x_2628_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2628_, 0, v_toCold_2614_);
lean_ctor_set(v___x_2628_, 1, v_options_2615_);
lean_ctor_set(v___x_2628_, 2, v_currRecDepth_2616_);
lean_ctor_set(v___x_2628_, 3, v_maxRecDepth_2617_);
lean_ctor_set(v___x_2628_, 4, v_ref_2627_);
lean_ctor_set(v___x_2628_, 5, v_currNamespace_2619_);
lean_ctor_set(v___x_2628_, 6, v_openDecls_2620_);
lean_ctor_set(v___x_2628_, 7, v_initHeartbeats_2621_);
lean_ctor_set(v___x_2628_, 8, v_maxHeartbeats_2622_);
lean_ctor_set(v___x_2628_, 9, v_currMacroScope_2623_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*10, v_diag_2624_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*10 + 1, v_suppressElabErrors_2625_);
v___x_2629_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2613_, v___x_2626_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v___x_2628_, v_a_2606_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; uint8_t v___x_2727_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_2630_, v_a_2604_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref(v___x_2631_);
v___x_2727_ = l_Lean_Expr_hasSorry(v_a_2632_);
if (v___x_2727_ == 0)
{
v___y_2672_ = v_a_2601_;
v___y_2673_ = v_a_2602_;
v___y_2674_ = v_a_2603_;
v___y_2675_ = v_a_2604_;
v___y_2676_ = v___x_2628_;
v___y_2677_ = v_a_2606_;
goto v___jp_2671_;
}
else
{
uint8_t v___x_2728_; 
v___x_2728_ = l_Lean_Expr_hasSyntheticSorry(v_a_2632_);
if (v___x_2728_ == 0)
{
v___y_2709_ = v_a_2601_;
v___y_2710_ = v_a_2602_;
v___y_2711_ = v_a_2603_;
v___y_2712_ = v_a_2604_;
v___y_2713_ = v___x_2628_;
v___y_2714_ = v_a_2606_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_a_2632_);
lean_dec_ref_known(v___x_2628_, 10);
v___x_2729_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
v___jp_2633_:
{
if (v___y_2643_ == 0)
{
if (lean_obj_tag(v___y_2637_) == 0)
{
lean_dec_ref_known(v___y_2637_, 2);
lean_dec_ref(v___y_2634_);
lean_dec(v_a_2632_);
return v___y_2641_;
}
else
{
lean_object* v_id_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2657_; 
v_id_2644_ = lean_ctor_get(v___y_2637_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___y_2637_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v___y_2637_, 1);
lean_dec(v_unused_2658_);
v___x_2646_ = v___y_2637_;
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_id_2644_);
lean_dec(v___y_2637_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2640_, v_id_2644_);
lean_dec(v_id_2644_);
if (v___x_2648_ == 0)
{
lean_del_object(v___x_2646_);
lean_dec_ref(v___y_2634_);
lean_dec(v_a_2632_);
return v___y_2641_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
lean_dec_ref(v___y_2641_);
v___x_2649_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_2650_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_2651_ = l_Lean_indentExpr(v_a_2632_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 7);
lean_ctor_set(v___x_2646_, 1, v___x_2651_);
lean_ctor_set(v___x_2646_, 0, v___x_2650_);
v___x_2653_ = v___x_2646_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___x_2649_);
v___x_2655_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2654_, v___y_2636_, v___y_2635_, v___y_2642_, v___y_2638_, v___y_2634_, v___y_2639_);
lean_dec_ref(v___y_2634_);
return v___x_2655_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2637_);
lean_dec_ref(v___y_2634_);
lean_dec(v_a_2632_);
return v___y_2641_;
}
}
v___jp_2659_:
{
lean_object* v___x_2666_; 
lean_inc(v_a_2632_);
v___x_2666_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2632_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec_ref(v___y_2664_);
lean_dec(v_a_2632_);
return v___x_2666_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
v___x_2668_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2669_ = l_Lean_Exception_isInterrupt(v_a_2667_);
if (v___x_2669_ == 0)
{
uint8_t v___x_2670_; 
lean_inc(v_a_2667_);
v___x_2670_ = l_Lean_Exception_isRuntime(v_a_2667_);
v___y_2634_ = v___y_2664_;
v___y_2635_ = v___y_2661_;
v___y_2636_ = v___y_2660_;
v___y_2637_ = v_a_2667_;
v___y_2638_ = v___y_2663_;
v___y_2639_ = v___y_2665_;
v___y_2640_ = v___x_2668_;
v___y_2641_ = v___x_2666_;
v___y_2642_ = v___y_2662_;
v___y_2643_ = v___x_2670_;
goto v___jp_2633_;
}
else
{
v___y_2634_ = v___y_2664_;
v___y_2635_ = v___y_2661_;
v___y_2636_ = v___y_2660_;
v___y_2637_ = v_a_2667_;
v___y_2638_ = v___y_2663_;
v___y_2639_ = v___y_2665_;
v___y_2640_ = v___x_2668_;
v___y_2641_ = v___x_2666_;
v___y_2642_ = v___y_2662_;
v___y_2643_ = v___x_2669_;
goto v___jp_2633_;
}
}
}
v___jp_2671_:
{
lean_object* v___x_2678_; 
lean_inc(v_a_2632_);
v___x_2678_ = l_Lean_Meta_getMVars(v_a_2632_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2679_, v___x_2610_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v_a_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; uint8_t v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_unbox(v_a_2681_);
lean_dec(v_a_2681_);
if (v___x_2682_ == 0)
{
v___y_2660_ = v___y_2672_;
v___y_2661_ = v___y_2673_;
v___y_2662_ = v___y_2674_;
v___y_2663_ = v___y_2675_;
v___y_2664_ = v___y_2676_;
v___y_2665_ = v___y_2677_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___y_2676_);
lean_dec(v_a_2632_);
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
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v___y_2676_);
lean_dec(v_a_2632_);
v_a_2692_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2680_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2680_);
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
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v___y_2676_);
lean_dec(v_a_2632_);
v_a_2700_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2678_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2678_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
v___jp_2708_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v___x_2715_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_2716_ = l_Lean_indentExpr(v_a_2632_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2717_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec_ref(v___y_2713_);
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref_known(v___x_2628_, 10);
v_a_2738_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2629_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2629_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_stx_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(lean_object* v_config_2757_, lean_object* v_item_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_item_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2777_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2758_, v___x_2776_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2777_) == 0)
{
uint8_t v___x_2778_; 
lean_dec_ref_known(v___x_2777_, 1);
v___x_2778_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_2758_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2779_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_2758_);
lean_inc_ref(v_item_2758_);
v___x_2780_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_2758_);
v___x_2781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_2782_ = lean_string_dec_lt(v___x_2779_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_2784_ = lean_string_dec_lt(v___x_2779_, v___x_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = lean_string_dec_eq(v___x_2779_, v___x_2783_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_2787_ = lean_string_dec_eq(v___x_2779_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_2789_ = lean_string_dec_eq(v___x_2779_, v___x_2788_);
lean_dec_ref(v___x_2779_);
if (v___x_2789_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_2791_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_2790_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2791_) == 0)
{
uint8_t v___x_2792_; 
lean_dec_ref_known(v___x_2791_, 1);
v___x_2792_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_2792_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2793_; 
lean_dec_ref(v___x_2780_);
v___x_2793_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2819_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2819_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2819_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
uint8_t v_proofs_2798_; uint8_t v_types_2799_; uint8_t v_implicits_2800_; uint8_t v_descend_2801_; uint8_t v_underBinder_2802_; uint8_t v_merge_2803_; uint8_t v_useContext_2804_; uint8_t v_onlyGivenNames_2805_; uint8_t v_preserveBinderNames_2806_; uint8_t v_lift_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2818_; 
v_proofs_2798_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_2799_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_2800_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_2801_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_2802_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_merge_2803_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_2804_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_2805_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_2806_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_2807_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2809_ = v_config_2757_;
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
else
{
lean_dec(v_config_2757_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, 0, v_proofs_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, 1, v_types_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, 2, v_implicits_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, 3, v_descend_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, 4, v_underBinder_2802_);
v___x_2812_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
uint8_t v___x_2813_; lean_object* v___x_2815_; 
v___x_2813_ = lean_unbox(v_a_2794_);
lean_dec(v_a_2794_);
lean_ctor_set_uint8(v___x_2812_, 5, v___x_2813_);
lean_ctor_set_uint8(v___x_2812_, 6, v_merge_2803_);
lean_ctor_set_uint8(v___x_2812_, 7, v_useContext_2804_);
lean_ctor_set_uint8(v___x_2812_, 8, v_onlyGivenNames_2805_);
lean_ctor_set_uint8(v___x_2812_, 9, v_preserveBinderNames_2806_);
lean_ctor_set_uint8(v___x_2812_, 10, v_lift_2807_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2812_);
v___x_2815_ = v___x_2796_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2812_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_config_2757_);
v_a_2820_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2793_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2793_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_2828_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2791_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2791_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec_ref(v___x_2779_);
v___x_2836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_2837_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_2836_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2837_) == 0)
{
uint8_t v___x_2838_; 
lean_dec_ref_known(v___x_2837_, 1);
v___x_2838_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_2838_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2839_; 
lean_dec_ref(v___x_2780_);
v___x_2839_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2865_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2865_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2865_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
uint8_t v_proofs_2844_; uint8_t v_types_2845_; uint8_t v_implicits_2846_; uint8_t v_descend_2847_; uint8_t v_underBinder_2848_; uint8_t v_usedOnly_2849_; uint8_t v_merge_2850_; uint8_t v_onlyGivenNames_2851_; uint8_t v_preserveBinderNames_2852_; uint8_t v_lift_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2864_; 
v_proofs_2844_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_2845_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_2846_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_2847_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_2848_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_2849_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_2850_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_onlyGivenNames_2851_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_2852_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_2853_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2855_ = v_config_2757_;
v_isShared_2856_ = v_isSharedCheck_2864_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_config_2757_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2864_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 0, v_proofs_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 1, v_types_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 2, v_implicits_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 3, v_descend_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 4, v_underBinder_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 5, v_usedOnly_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, 6, v_merge_2850_);
v___x_2858_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
uint8_t v___x_2859_; lean_object* v___x_2861_; 
v___x_2859_ = lean_unbox(v_a_2840_);
lean_dec(v_a_2840_);
lean_ctor_set_uint8(v___x_2858_, 7, v___x_2859_);
lean_ctor_set_uint8(v___x_2858_, 8, v_onlyGivenNames_2851_);
lean_ctor_set_uint8(v___x_2858_, 9, v_preserveBinderNames_2852_);
lean_ctor_set_uint8(v___x_2858_, 10, v_lift_2853_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2858_);
v___x_2861_ = v___x_2842_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2858_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_config_2757_);
v_a_2866_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2839_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2839_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_2874_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2837_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2837_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref(v___x_2779_);
v___x_2882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_2883_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_2882_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2883_) == 0)
{
uint8_t v___x_2884_; 
lean_dec_ref_known(v___x_2883_, 1);
v___x_2884_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_2884_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2885_; 
lean_dec_ref(v___x_2780_);
v___x_2885_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2911_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2911_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2911_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint8_t v_proofs_2890_; uint8_t v_types_2891_; uint8_t v_implicits_2892_; uint8_t v_descend_2893_; uint8_t v_usedOnly_2894_; uint8_t v_merge_2895_; uint8_t v_useContext_2896_; uint8_t v_onlyGivenNames_2897_; uint8_t v_preserveBinderNames_2898_; uint8_t v_lift_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2910_; 
v_proofs_2890_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_2891_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_2892_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_2893_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_usedOnly_2894_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_2895_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_2896_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_2897_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_2898_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_2899_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2901_ = v_config_2757_;
v_isShared_2902_ = v_isSharedCheck_2910_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v_config_2757_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2910_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2909_, 0, v_proofs_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2909_, 1, v_types_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2909_, 2, v_implicits_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2909_, 3, v_descend_2893_);
v___x_2904_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
uint8_t v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = lean_unbox(v_a_2886_);
lean_dec(v_a_2886_);
lean_ctor_set_uint8(v___x_2904_, 4, v___x_2905_);
lean_ctor_set_uint8(v___x_2904_, 5, v_usedOnly_2894_);
lean_ctor_set_uint8(v___x_2904_, 6, v_merge_2895_);
lean_ctor_set_uint8(v___x_2904_, 7, v_useContext_2896_);
lean_ctor_set_uint8(v___x_2904_, 8, v_onlyGivenNames_2897_);
lean_ctor_set_uint8(v___x_2904_, 9, v_preserveBinderNames_2898_);
lean_ctor_set_uint8(v___x_2904_, 10, v_lift_2899_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2904_);
v___x_2907_ = v___x_2888_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2904_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v_config_2757_);
v_a_2912_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2885_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2885_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_2920_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2883_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2883_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_string_dec_eq(v___x_2779_, v___x_2781_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_2930_ = lean_string_dec_eq(v___x_2779_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_2932_ = lean_string_dec_eq(v___x_2779_, v___x_2931_);
lean_dec_ref(v___x_2779_);
if (v___x_2932_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_2934_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_2933_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2934_) == 0)
{
uint8_t v___x_2935_; 
lean_dec_ref_known(v___x_2934_, 1);
v___x_2935_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_2935_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2936_; 
lean_dec_ref(v___x_2780_);
v___x_2936_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2962_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2962_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2962_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
uint8_t v_proofs_2941_; uint8_t v_implicits_2942_; uint8_t v_descend_2943_; uint8_t v_underBinder_2944_; uint8_t v_usedOnly_2945_; uint8_t v_merge_2946_; uint8_t v_useContext_2947_; uint8_t v_onlyGivenNames_2948_; uint8_t v_preserveBinderNames_2949_; uint8_t v_lift_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2961_; 
v_proofs_2941_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_implicits_2942_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_2943_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_2944_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_2945_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_2946_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_2947_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_2948_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_2949_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_2950_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2952_ = v_config_2757_;
v_isShared_2953_ = v_isSharedCheck_2961_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_config_2757_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2961_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2960_, 0, v_proofs_2941_);
v___x_2955_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
uint8_t v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = lean_unbox(v_a_2937_);
lean_dec(v_a_2937_);
lean_ctor_set_uint8(v___x_2955_, 1, v___x_2956_);
lean_ctor_set_uint8(v___x_2955_, 2, v_implicits_2942_);
lean_ctor_set_uint8(v___x_2955_, 3, v_descend_2943_);
lean_ctor_set_uint8(v___x_2955_, 4, v_underBinder_2944_);
lean_ctor_set_uint8(v___x_2955_, 5, v_usedOnly_2945_);
lean_ctor_set_uint8(v___x_2955_, 6, v_merge_2946_);
lean_ctor_set_uint8(v___x_2955_, 7, v_useContext_2947_);
lean_ctor_set_uint8(v___x_2955_, 8, v_onlyGivenNames_2948_);
lean_ctor_set_uint8(v___x_2955_, 9, v_preserveBinderNames_2949_);
lean_ctor_set_uint8(v___x_2955_, 10, v_lift_2950_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2955_);
v___x_2958_ = v___x_2939_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2955_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_config_2757_);
v_a_2963_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2936_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2936_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_2971_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2934_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2934_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec_ref(v___x_2779_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_2980_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_2979_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2980_) == 0)
{
uint8_t v___x_2981_; 
lean_dec_ref_known(v___x_2980_, 1);
v___x_2981_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2982_; 
lean_dec_ref(v___x_2780_);
v___x_2982_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3008_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3008_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3008_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
uint8_t v_types_2987_; uint8_t v_implicits_2988_; uint8_t v_descend_2989_; uint8_t v_underBinder_2990_; uint8_t v_usedOnly_2991_; uint8_t v_merge_2992_; uint8_t v_useContext_2993_; uint8_t v_onlyGivenNames_2994_; uint8_t v_preserveBinderNames_2995_; uint8_t v_lift_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3007_; 
v_types_2987_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_2988_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_2989_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_2990_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_2991_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_2992_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_2993_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_2994_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_2995_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_2996_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2998_ = v_config_2757_;
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
else
{
lean_dec(v_config_2757_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 0, 11);
v___x_3001_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
uint8_t v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = lean_unbox(v_a_2983_);
lean_dec(v_a_2983_);
lean_ctor_set_uint8(v___x_3001_, 0, v___x_3002_);
lean_ctor_set_uint8(v___x_3001_, 1, v_types_2987_);
lean_ctor_set_uint8(v___x_3001_, 2, v_implicits_2988_);
lean_ctor_set_uint8(v___x_3001_, 3, v_descend_2989_);
lean_ctor_set_uint8(v___x_3001_, 4, v_underBinder_2990_);
lean_ctor_set_uint8(v___x_3001_, 5, v_usedOnly_2991_);
lean_ctor_set_uint8(v___x_3001_, 6, v_merge_2992_);
lean_ctor_set_uint8(v___x_3001_, 7, v_useContext_2993_);
lean_ctor_set_uint8(v___x_3001_, 8, v_onlyGivenNames_2994_);
lean_ctor_set_uint8(v___x_3001_, 9, v_preserveBinderNames_2995_);
lean_ctor_set_uint8(v___x_3001_, 10, v_lift_2996_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_3001_);
v___x_3004_ = v___x_2985_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3001_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_config_2757_);
v_a_3009_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2982_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2982_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3017_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2980_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2980_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v___x_2779_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_3026_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3025_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3026_) == 0)
{
uint8_t v___x_3027_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3027_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3028_; 
lean_dec_ref(v___x_2780_);
v___x_3028_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3054_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3054_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3054_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
uint8_t v_proofs_3033_; uint8_t v_types_3034_; uint8_t v_implicits_3035_; uint8_t v_descend_3036_; uint8_t v_underBinder_3037_; uint8_t v_usedOnly_3038_; uint8_t v_merge_3039_; uint8_t v_useContext_3040_; uint8_t v_onlyGivenNames_3041_; uint8_t v_lift_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3053_; 
v_proofs_3033_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3034_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_3035_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_3036_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_3037_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3038_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_3039_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_3040_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_3041_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_lift_3042_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3044_ = v_config_2757_;
v_isShared_3045_ = v_isSharedCheck_3053_;
goto v_resetjp_3043_;
}
else
{
lean_dec(v_config_2757_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3053_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 0, v_proofs_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 1, v_types_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 2, v_implicits_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 3, v_descend_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 4, v_underBinder_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 5, v_usedOnly_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 6, v_merge_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 7, v_useContext_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, 8, v_onlyGivenNames_3041_);
v___x_3047_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
uint8_t v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_unbox(v_a_3029_);
lean_dec(v_a_3029_);
lean_ctor_set_uint8(v___x_3047_, 9, v___x_3048_);
lean_ctor_set_uint8(v___x_3047_, 10, v_lift_3042_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3047_);
v___x_3050_ = v___x_3031_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3047_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v_config_2757_);
v_a_3055_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3028_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3028_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3063_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3026_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3026_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
else
{
lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_3072_ = lean_string_dec_lt(v___x_2779_, v___x_3071_);
if (v___x_3072_ == 0)
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_string_dec_eq(v___x_2779_, v___x_3071_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_3075_ = lean_string_dec_eq(v___x_2779_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_3077_ = lean_string_dec_eq(v___x_2779_, v___x_3076_);
lean_dec_ref(v___x_2779_);
if (v___x_3077_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_3079_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3078_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3079_) == 0)
{
uint8_t v___x_3080_; 
lean_dec_ref_known(v___x_3079_, 1);
v___x_3080_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3080_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3081_; 
lean_dec_ref(v___x_2780_);
v___x_3081_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3107_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3107_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3107_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
uint8_t v_proofs_3086_; uint8_t v_types_3087_; uint8_t v_implicits_3088_; uint8_t v_descend_3089_; uint8_t v_underBinder_3090_; uint8_t v_usedOnly_3091_; uint8_t v_merge_3092_; uint8_t v_useContext_3093_; uint8_t v_preserveBinderNames_3094_; uint8_t v_lift_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3106_; 
v_proofs_3086_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3087_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_3088_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_3089_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_3090_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3091_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_3092_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_3093_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_preserveBinderNames_3094_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_3095_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3097_ = v_config_2757_;
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v_config_2757_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 0, v_proofs_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 1, v_types_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 2, v_implicits_3088_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 3, v_descend_3089_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 4, v_underBinder_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 5, v_usedOnly_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 6, v_merge_3092_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, 7, v_useContext_3093_);
v___x_3100_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
uint8_t v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_unbox(v_a_3082_);
lean_dec(v_a_3082_);
lean_ctor_set_uint8(v___x_3100_, 8, v___x_3101_);
lean_ctor_set_uint8(v___x_3100_, 9, v_preserveBinderNames_3094_);
lean_ctor_set_uint8(v___x_3100_, 10, v_lift_3095_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3100_);
v___x_3103_ = v___x_3084_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3100_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v_config_2757_);
v_a_3108_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3081_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3081_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3116_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3079_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3079_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec_ref(v___x_2779_);
v___x_3124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_3125_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3124_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3125_) == 0)
{
uint8_t v___x_3126_; 
lean_dec_ref_known(v___x_3125_, 1);
v___x_3126_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3126_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3127_; 
lean_dec_ref(v___x_2780_);
v___x_3127_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3153_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3153_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3153_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
uint8_t v_proofs_3132_; uint8_t v_types_3133_; uint8_t v_implicits_3134_; uint8_t v_descend_3135_; uint8_t v_underBinder_3136_; uint8_t v_usedOnly_3137_; uint8_t v_useContext_3138_; uint8_t v_onlyGivenNames_3139_; uint8_t v_preserveBinderNames_3140_; uint8_t v_lift_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3152_; 
v_proofs_3132_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3133_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_3134_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_3135_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_3136_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3137_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_useContext_3138_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_3139_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_3140_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_3141_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3143_ = v_config_2757_;
v_isShared_3144_ = v_isSharedCheck_3152_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v_config_2757_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3152_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 0, v_proofs_3132_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 1, v_types_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 2, v_implicits_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 3, v_descend_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 4, v_underBinder_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, 5, v_usedOnly_3137_);
v___x_3146_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
uint8_t v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_unbox(v_a_3128_);
lean_dec(v_a_3128_);
lean_ctor_set_uint8(v___x_3146_, 6, v___x_3147_);
lean_ctor_set_uint8(v___x_3146_, 7, v_useContext_3138_);
lean_ctor_set_uint8(v___x_3146_, 8, v_onlyGivenNames_3139_);
lean_ctor_set_uint8(v___x_3146_, 9, v_preserveBinderNames_3140_);
lean_ctor_set_uint8(v___x_3146_, 10, v_lift_3141_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3146_);
v___x_3149_ = v___x_3130_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3146_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v_config_2757_);
v_a_3154_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3127_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3127_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3162_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3125_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3125_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec_ref(v___x_2779_);
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_3171_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3170_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3171_) == 0)
{
uint8_t v___x_3172_; 
lean_dec_ref_known(v___x_3171_, 1);
v___x_3172_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3173_; 
lean_dec_ref(v___x_2780_);
v___x_3173_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
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
uint8_t v_proofs_3178_; uint8_t v_types_3179_; uint8_t v_implicits_3180_; uint8_t v_descend_3181_; uint8_t v_underBinder_3182_; uint8_t v_usedOnly_3183_; uint8_t v_merge_3184_; uint8_t v_useContext_3185_; uint8_t v_onlyGivenNames_3186_; uint8_t v_preserveBinderNames_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3198_; 
v_proofs_3178_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3179_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_3180_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_descend_3181_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_3182_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3183_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_3184_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_3185_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_3186_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_3187_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3189_ = v_config_2757_;
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
else
{
lean_dec(v_config_2757_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 2, v_implicits_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 3, v_descend_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 4, v_underBinder_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 5, v_usedOnly_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 6, v_merge_3184_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 7, v_useContext_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 8, v_onlyGivenNames_3186_);
lean_ctor_set_uint8(v_reuseFailAlloc_3197_, 9, v_preserveBinderNames_3187_);
v___x_3192_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
uint8_t v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_unbox(v_a_3174_);
lean_dec(v_a_3174_);
lean_ctor_set_uint8(v___x_3192_, 10, v___x_3193_);
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
lean_dec_ref(v_config_2757_);
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
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
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
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_3217_ = lean_string_dec_eq(v___x_2779_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_3219_ = lean_string_dec_eq(v___x_2779_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_3221_ = lean_string_dec_eq(v___x_2779_, v___x_3220_);
lean_dec_ref(v___x_2779_);
if (v___x_3221_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_3223_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3222_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3223_) == 0)
{
uint8_t v___x_3224_; 
lean_dec_ref_known(v___x_3223_, 1);
v___x_3224_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3224_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3225_; 
lean_dec_ref(v___x_2780_);
v___x_3225_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3251_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3251_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3251_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
uint8_t v_proofs_3230_; uint8_t v_types_3231_; uint8_t v_descend_3232_; uint8_t v_underBinder_3233_; uint8_t v_usedOnly_3234_; uint8_t v_merge_3235_; uint8_t v_useContext_3236_; uint8_t v_onlyGivenNames_3237_; uint8_t v_preserveBinderNames_3238_; uint8_t v_lift_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3250_; 
v_proofs_3230_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3231_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_descend_3232_ = lean_ctor_get_uint8(v_config_2757_, 3);
v_underBinder_3233_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3234_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_3235_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_3236_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_3237_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_3238_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_3239_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3241_ = v_config_2757_;
v_isShared_3242_ = v_isSharedCheck_3250_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v_config_2757_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3250_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3249_, 0, v_proofs_3230_);
lean_ctor_set_uint8(v_reuseFailAlloc_3249_, 1, v_types_3231_);
v___x_3244_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
uint8_t v___x_3245_; lean_object* v___x_3247_; 
v___x_3245_ = lean_unbox(v_a_3226_);
lean_dec(v_a_3226_);
lean_ctor_set_uint8(v___x_3244_, 2, v___x_3245_);
lean_ctor_set_uint8(v___x_3244_, 3, v_descend_3232_);
lean_ctor_set_uint8(v___x_3244_, 4, v_underBinder_3233_);
lean_ctor_set_uint8(v___x_3244_, 5, v_usedOnly_3234_);
lean_ctor_set_uint8(v___x_3244_, 6, v_merge_3235_);
lean_ctor_set_uint8(v___x_3244_, 7, v_useContext_3236_);
lean_ctor_set_uint8(v___x_3244_, 8, v_onlyGivenNames_3237_);
lean_ctor_set_uint8(v___x_3244_, 9, v_preserveBinderNames_3238_);
lean_ctor_set_uint8(v___x_3244_, 10, v_lift_3239_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3244_);
v___x_3247_ = v___x_3228_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3244_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_config_2757_);
v_a_3252_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3225_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3225_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3260_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3223_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3223_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec_ref(v___x_2779_);
v___x_3268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_3269_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2758_, v___x_3268_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3269_) == 0)
{
uint8_t v___x_3270_; 
lean_dec_ref_known(v___x_3269_, 1);
v___x_3270_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3270_ == 0)
{
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_3271_; 
lean_dec_ref(v___x_2780_);
v___x_3271_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3297_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3297_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3297_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
uint8_t v_proofs_3276_; uint8_t v_types_3277_; uint8_t v_implicits_3278_; uint8_t v_underBinder_3279_; uint8_t v_usedOnly_3280_; uint8_t v_merge_3281_; uint8_t v_useContext_3282_; uint8_t v_onlyGivenNames_3283_; uint8_t v_preserveBinderNames_3284_; uint8_t v_lift_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3296_; 
v_proofs_3276_ = lean_ctor_get_uint8(v_config_2757_, 0);
v_types_3277_ = lean_ctor_get_uint8(v_config_2757_, 1);
v_implicits_3278_ = lean_ctor_get_uint8(v_config_2757_, 2);
v_underBinder_3279_ = lean_ctor_get_uint8(v_config_2757_, 4);
v_usedOnly_3280_ = lean_ctor_get_uint8(v_config_2757_, 5);
v_merge_3281_ = lean_ctor_get_uint8(v_config_2757_, 6);
v_useContext_3282_ = lean_ctor_get_uint8(v_config_2757_, 7);
v_onlyGivenNames_3283_ = lean_ctor_get_uint8(v_config_2757_, 8);
v_preserveBinderNames_3284_ = lean_ctor_get_uint8(v_config_2757_, 9);
v_lift_3285_ = lean_ctor_get_uint8(v_config_2757_, 10);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_config_2757_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3287_ = v_config_2757_;
v_isShared_3288_ = v_isSharedCheck_3296_;
goto v_resetjp_3286_;
}
else
{
lean_dec(v_config_2757_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3296_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3295_, 0, v_proofs_3276_);
lean_ctor_set_uint8(v_reuseFailAlloc_3295_, 1, v_types_3277_);
lean_ctor_set_uint8(v_reuseFailAlloc_3295_, 2, v_implicits_3278_);
v___x_3290_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
uint8_t v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_unbox(v_a_3272_);
lean_dec(v_a_3272_);
lean_ctor_set_uint8(v___x_3290_, 3, v___x_3291_);
lean_ctor_set_uint8(v___x_3290_, 4, v_underBinder_3279_);
lean_ctor_set_uint8(v___x_3290_, 5, v_usedOnly_3280_);
lean_ctor_set_uint8(v___x_3290_, 6, v_merge_3281_);
lean_ctor_set_uint8(v___x_3290_, 7, v_useContext_3282_);
lean_ctor_set_uint8(v___x_3290_, 8, v_onlyGivenNames_3283_);
lean_ctor_set_uint8(v___x_3290_, 9, v_preserveBinderNames_3284_);
lean_ctor_set_uint8(v___x_3290_, 10, v_lift_3285_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3290_);
v___x_3293_ = v___x_3274_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3290_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_config_2757_);
v_a_3298_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3271_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3271_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3306_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3269_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3269_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
else
{
uint8_t v___x_3314_; 
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_config_2757_);
v___x_3314_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2780_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v_item_2758_);
v_item_2767_ = v___x_2780_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
else
{
lean_object* v_value_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___x_2780_);
v_value_3315_ = lean_ctor_get(v_item_2758_, 2);
lean_inc(v_value_3315_);
lean_dec_ref(v_item_2758_);
v___x_3316_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_value_3315_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_3316_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_2757_);
v_item_2767_ = v_item_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
v___y_2770_ = v___y_2761_;
v___y_2771_ = v___y_2762_;
v___y_2772_ = v___y_2763_;
v___y_2773_ = v___y_2764_;
goto v___jp_2766_;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v_item_2758_);
lean_dec_ref(v_config_2757_);
v_a_3317_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_2777_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_2777_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
v___jp_2766_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_2775_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_2767_, v___x_2774_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3325_, lean_object* v_item_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(v_config_3325_, v_item_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_3339_ = l_Lean_mkConst(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(lean_object* v_cfg_3342_, lean_object* v_cfgItem_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1);
v___x_3352_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3342_, v_cfgItem_3343_, v___x_3351_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_3353_, lean_object* v_cfgItem_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(v_cfg_3353_, v_cfgItem_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v_cfgItem_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_cfg_3364_, lean_object* v_init_3365_, uint8_t v_logExceptions_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_onErr_3371_; lean_object* v_eval_3372_; 
v_onErr_3371_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0));
v_eval_3372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_3366_ == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3372_, v_init_3365_, v_cfg_3364_, v_onErr_3371_, v_logExceptions_3366_, v_a_3368_, v_a_3369_);
return v___x_3373_;
}
else
{
uint8_t v_recover_3374_; lean_object* v___x_3375_; 
v_recover_3374_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*1);
v___x_3375_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3372_, v_init_3365_, v_cfg_3364_, v_onErr_3371_, v_recover_3374_, v_a_3368_, v_a_3369_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_cfg_3376_, lean_object* v_init_3377_, lean_object* v_logExceptions_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
uint8_t v_logExceptions_boxed_3383_; lean_object* v_res_3384_; 
v_logExceptions_boxed_3383_ = lean_unbox(v_logExceptions_3378_);
v_res_3384_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3376_, v_init_3377_, v_logExceptions_boxed_3383_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_a_3379_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_cfg_3385_, lean_object* v_init_3386_, uint8_t v_logExceptions_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3385_, v_init_3386_, v_logExceptions_3387_, v_a_3388_, v_a_3394_, v_a_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_cfg_3398_, lean_object* v_init_3399_, lean_object* v_logExceptions_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
uint8_t v_logExceptions_boxed_3410_; lean_object* v_res_3411_; 
v_logExceptions_boxed_3410_ = lean_unbox(v_logExceptions_3400_);
v_res_3411_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_cfg_3398_, v_init_3399_, v_logExceptions_boxed_3410_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
return v_res_3411_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_3426_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_3425_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v_x_3427_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3440_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = l_Lean_MVarId_liftLets(v_a_3449_, v_a_3438_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3453_, 0, v_a_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3453_, v___y_3440_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
return v___x_3454_;
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_a_3455_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3450_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3450_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v_a_3438_);
v_a_3463_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3448_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3448_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_3504_, lean_object* v_a_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3507_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_3516_, v_h_3504_, v_a_3505_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3520_, 0, v_a_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3520_, v___y_3507_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
return v___x_3521_;
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
v_a_3522_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3517_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v_a_3505_);
lean_dec(v_h_3504_);
v_a_3530_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3515_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3515_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_3538_, lean_object* v_a_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_3538_, v_a_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_3550_, lean_object* v_h_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___f_3561_; lean_object* v___x_3562_; 
v___f_3561_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3561_, 0, v_h_3551_);
lean_closure_set(v___f_3561_, 1, v_a_3550_);
v___x_3562_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3561_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_3563_, lean_object* v_h_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_3563_, v_h_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_3582_);
v___x_3593_ = l_Lean_Syntax_isOfKind(v_x_3582_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; 
lean_dec(v_x_3582_);
v___x_3594_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3594_;
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3595_ = lean_unsigned_to_nat(1u);
v___x_3596_ = l_Lean_Syntax_getArg(v_x_3582_, v___x_3595_);
v___x_3597_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_3596_);
v___x_3598_ = l_Lean_Syntax_isOfKind(v___x_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; 
lean_dec(v___x_3596_);
lean_dec(v_x_3582_);
v___x_3599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3599_;
}
else
{
lean_object* v___f_3600_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v_loc_x3f_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___f_3600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_3650_ = lean_unsigned_to_nat(2u);
v___x_3651_ = l_Lean_Syntax_getArg(v_x_3582_, v___x_3650_);
lean_dec(v_x_3582_);
v___x_3652_ = l_Lean_Syntax_isNone(v___x_3651_);
if (v___x_3652_ == 0)
{
uint8_t v___x_3653_; 
lean_inc(v___x_3651_);
v___x_3653_ = l_Lean_Syntax_matchesNull(v___x_3651_, v___x_3595_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; 
lean_dec(v___x_3651_);
lean_dec(v___x_3596_);
v___x_3654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3654_;
}
else
{
lean_object* v___x_3655_; lean_object* v_loc_x3f_3656_; 
v___x_3655_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3656_ = l_Lean_Syntax_getArg(v___x_3651_, v___x_3655_);
lean_dec(v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3656_);
v___x_3660_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3656_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec(v_loc_x3f_3656_);
lean_dec(v___x_3596_);
v___x_3661_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3661_;
}
else
{
goto v___jp_3657_;
}
}
else
{
goto v___jp_3657_;
}
v___jp_3657_:
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_loc_x3f_3656_);
v_loc_x3f_3617_ = v___x_3658_;
v___y_3618_ = v_a_3583_;
v___y_3619_ = v_a_3584_;
v___y_3620_ = v_a_3585_;
v___y_3621_ = v_a_3586_;
v___y_3622_ = v_a_3587_;
v___y_3623_ = v_a_3588_;
v___y_3624_ = v_a_3589_;
v___y_3625_ = v_a_3590_;
goto v___jp_3616_;
}
}
}
else
{
lean_object* v___x_3662_; 
lean_dec(v___x_3651_);
v___x_3662_ = lean_box(0);
v_loc_x3f_3617_ = v___x_3662_;
v___y_3618_ = v_a_3583_;
v___y_3619_ = v_a_3584_;
v___y_3620_ = v_a_3585_;
v___y_3621_ = v_a_3586_;
v___y_3622_ = v_a_3587_;
v___y_3623_ = v_a_3588_;
v___y_3624_ = v_a_3589_;
v___y_3625_ = v_a_3590_;
goto v___jp_3616_;
}
v___jp_3601_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = l_Lean_mkOptionalNode(v___y_3612_);
v___x_3614_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3613_);
lean_dec(v___x_3613_);
v___x_3615_ = l_Lean_Elab_Tactic_withLocation(v___x_3614_, v___y_3610_, v___y_3602_, v___f_3600_, v___y_3611_, v___y_3605_, v___y_3604_, v___y_3603_, v___y_3609_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___x_3614_);
return v___x_3615_;
}
v___jp_3616_:
{
uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = 0;
v___x_3627_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_3627_, 0, v___x_3626_);
lean_ctor_set_uint8(v___x_3627_, 1, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 2, v___x_3626_);
lean_ctor_set_uint8(v___x_3627_, 3, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 4, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 5, v___x_3626_);
lean_ctor_set_uint8(v___x_3627_, 6, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 7, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 8, v___x_3626_);
lean_ctor_set_uint8(v___x_3627_, 9, v___x_3598_);
lean_ctor_set_uint8(v___x_3627_, 10, v___x_3598_);
v___x_3628_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_3596_, v___x_3627_, v___x_3598_, v___y_3618_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___f_3630_; lean_object* v___f_3631_; lean_object* v___f_3632_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc_n(v_a_3629_, 2);
lean_dec_ref_known(v___x_3628_, 1);
v___f_3630_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3630_, 0, v_a_3629_);
v___f_3631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3631_, 0, v___f_3630_);
v___f_3632_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_3632_, 0, v_a_3629_);
if (lean_obj_tag(v_loc_x3f_3617_) == 0)
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_box(0);
v___y_3602_ = v___f_3631_;
v___y_3603_ = v___y_3621_;
v___y_3604_ = v___y_3620_;
v___y_3605_ = v___y_3619_;
v___y_3606_ = v___y_3623_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3625_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v___f_3632_;
v___y_3611_ = v___y_3618_;
v___y_3612_ = v___x_3633_;
goto v___jp_3601_;
}
else
{
lean_object* v_val_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
v_val_3634_ = lean_ctor_get(v_loc_x3f_3617_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_loc_x3f_3617_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v_loc_x3f_3617_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_val_3634_);
lean_dec(v_loc_x3f_3617_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_val_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
v___y_3602_ = v___f_3631_;
v___y_3603_ = v___y_3621_;
v___y_3604_ = v___y_3620_;
v___y_3605_ = v___y_3619_;
v___y_3606_ = v___y_3623_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3625_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v___f_3632_;
v___y_3611_ = v___y_3618_;
v___y_3612_ = v___x_3639_;
goto v___jp_3601_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v_loc_x3f_3617_);
v_a_3642_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3628_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3628_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3681_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_3684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_3685_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3681_, v___x_3682_, v___x_3683_, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_3687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_3702_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(v___x_3701_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v_x_3703_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(lean_object* v_h_3714_, uint8_t v___x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3717_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v___x_3727_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_3726_, v_h_3714_, v___x_3715_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3730_, v___y_3717_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
return v___x_3731_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_a_3732_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3727_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3727_);
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
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v_h_3714_);
v_a_3740_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3725_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3725_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v_h_3748_, lean_object* v___x_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
uint8_t v___x_1028__boxed_3759_; lean_object* v_res_3760_; 
v___x_1028__boxed_3759_ = lean_unbox(v___x_3749_);
v_res_3760_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v_h_3748_, v___x_1028__boxed_3759_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_3761_, lean_object* v_h_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_box(v___x_3761_);
v___f_3773_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3773_, 0, v_h_3762_);
lean_closure_set(v___f_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3773_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_3775_, lean_object* v_h_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v___x_1104__boxed_3786_; lean_object* v_res_3787_; 
v___x_1104__boxed_3786_ = lean_unbox(v___x_3775_);
v_res_3787_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1104__boxed_3786_, v_h_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(uint8_t v___x_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3790_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3800_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___x_3800_ = l_Lean_MVarId_letToHave(v_a_3799_, v___x_3788_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3803_, v___y_3790_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3804_;
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
v_a_3805_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3800_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3800_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3798_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3798_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v___x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
uint8_t v___x_1140__boxed_3831_; lean_object* v_res_3832_; 
v___x_1140__boxed_3831_ = lean_unbox(v___x_3821_);
v_res_3832_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v___x_1140__boxed_3831_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_3840_);
v___x_3851_ = l_Lean_Syntax_isOfKind(v_x_3840_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
lean_dec(v_x_3840_);
v___x_3852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3852_;
}
else
{
lean_object* v___f_3853_; lean_object* v___x_3854_; lean_object* v___f_3855_; lean_object* v___x_3856_; lean_object* v___f_3857_; lean_object* v___f_3858_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v_val_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___f_3853_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_3854_ = lean_box(v___x_3851_);
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_3855_, 0, v___x_3854_);
v___x_3856_ = lean_box(v___x_3851_);
v___f_3857_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 10, 1);
lean_closure_set(v___f_3857_, 0, v___x_3856_);
v___f_3858_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3858_, 0, v___f_3857_);
v___x_3883_ = lean_unsigned_to_nat(1u);
v___x_3884_ = l_Lean_Syntax_getArg(v_x_3840_, v___x_3883_);
lean_dec(v_x_3840_);
v___x_3885_ = l_Lean_Syntax_isNone(v___x_3884_);
if (v___x_3885_ == 0)
{
uint8_t v___x_3886_; 
lean_inc(v___x_3884_);
v___x_3886_ = l_Lean_Syntax_matchesNull(v___x_3884_, v___x_3883_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; 
lean_dec(v___x_3884_);
lean_dec_ref(v___f_3858_);
lean_dec_ref(v___f_3855_);
v___x_3887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3887_;
}
else
{
lean_object* v___x_3888_; lean_object* v_loc_x3f_3889_; 
v___x_3888_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3889_ = l_Lean_Syntax_getArg(v___x_3884_, v___x_3888_);
lean_dec(v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3889_);
v___x_3891_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3889_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
lean_dec(v_loc_x3f_3889_);
lean_dec_ref(v___f_3858_);
lean_dec_ref(v___f_3855_);
v___x_3892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg();
return v___x_3892_;
}
else
{
v_val_3873_ = v_loc_x3f_3889_;
v___y_3874_ = v_a_3841_;
v___y_3875_ = v_a_3842_;
v___y_3876_ = v_a_3843_;
v___y_3877_ = v_a_3844_;
v___y_3878_ = v_a_3845_;
v___y_3879_ = v_a_3846_;
v___y_3880_ = v_a_3847_;
v___y_3881_ = v_a_3848_;
goto v___jp_3872_;
}
}
else
{
v_val_3873_ = v_loc_x3f_3889_;
v___y_3874_ = v_a_3841_;
v___y_3875_ = v_a_3842_;
v___y_3876_ = v_a_3843_;
v___y_3877_ = v_a_3844_;
v___y_3878_ = v_a_3845_;
v___y_3879_ = v_a_3846_;
v___y_3880_ = v_a_3847_;
v___y_3881_ = v_a_3848_;
goto v___jp_3872_;
}
}
}
else
{
lean_object* v___x_3893_; 
lean_dec(v___x_3884_);
v___x_3893_ = lean_box(0);
v___y_3860_ = v_a_3846_;
v___y_3861_ = v_a_3848_;
v___y_3862_ = v_a_3847_;
v___y_3863_ = v_a_3842_;
v___y_3864_ = v_a_3844_;
v___y_3865_ = v_a_3841_;
v___y_3866_ = v_a_3845_;
v___y_3867_ = v_a_3843_;
v___y_3868_ = v___x_3893_;
goto v___jp_3859_;
}
v___jp_3859_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = l_Lean_mkOptionalNode(v___y_3868_);
v___x_3870_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3869_);
lean_dec(v___x_3869_);
v___x_3871_ = l_Lean_Elab_Tactic_withLocation(v___x_3870_, v___f_3855_, v___f_3858_, v___f_3853_, v___y_3865_, v___y_3863_, v___y_3867_, v___y_3864_, v___y_3866_, v___y_3860_, v___y_3862_, v___y_3861_);
lean_dec(v___x_3870_);
return v___x_3871_;
}
v___jp_3872_:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v_val_3873_);
v___y_3860_ = v___y_3879_;
v___y_3861_ = v___y_3881_;
v___y_3862_ = v___y_3880_;
v___y_3863_ = v___y_3875_;
v___y_3864_ = v___y_3877_;
v___y_3865_ = v___y_3874_;
v___y_3866_ = v___y_3878_;
v___y_3867_ = v___y_3876_;
v___y_3868_ = v___x_3882_;
goto v___jp_3859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3912_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_3914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_3915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_3916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3912_, v___x_3913_, v___x_3914_, v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_3918_;
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
