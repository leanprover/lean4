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
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_6510__boxed_137_; uint8_t v_suppressElabErrors_boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v___y_6510__boxed_137_ = lean_unbox(v___y_134_);
v_suppressElabErrors_boxed_138_ = lean_unbox(v_suppressElabErrors_135_);
v_res_139_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v___y_6510__boxed_137_, v_suppressElabErrors_boxed_138_, v_x_136_);
lean_dec(v_x_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_142_, lean_object* v_msgData_143_, uint8_t v_severity_144_, uint8_t v_isSilent_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; uint8_t v___y_191_; uint8_t v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_213_; lean_object* v___y_214_; uint8_t v___y_215_; uint8_t v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_224_; lean_object* v___y_225_; uint8_t v___y_226_; uint8_t v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; uint8_t v___y_230_; uint8_t v___x_235_; lean_object* v___y_237_; lean_object* v___y_238_; uint8_t v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; uint8_t v___y_243_; uint8_t v___y_245_; uint8_t v___x_260_; 
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
lean_ctor_set(v___x_177_, 1, v___y_157_);
lean_inc_ref(v___y_154_);
lean_inc_ref(v___y_156_);
v___x_178_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_178_, 0, v___y_156_);
lean_ctor_set(v___x_178_, 1, v___y_153_);
lean_ctor_set(v___x_178_, 2, v___y_155_);
lean_ctor_set(v___x_178_, 3, v___y_154_);
lean_ctor_set(v___x_178_, 4, v___x_177_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*5, v___y_152_);
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
lean_inc_ref_n(v___y_190_, 2);
v___x_202_ = l_Lean_FileMap_toPosition(v___y_190_, v___y_189_);
lean_dec(v___y_189_);
v___x_203_ = l_Lean_FileMap_toPosition(v___y_190_, v___y_195_);
lean_dec(v___y_195_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_192_ == 0)
{
lean_del_object(v___x_200_);
lean_dec_ref(v___y_188_);
v___y_152_ = v___y_191_;
v___y_153_ = v___x_202_;
v___y_154_ = v___x_205_;
v___y_155_ = v___x_204_;
v___y_156_ = v___y_193_;
v___y_157_ = v_a_198_;
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
v___y_152_ = v___y_191_;
v___y_153_ = v___x_202_;
v___y_154_ = v___x_205_;
v___y_155_ = v___x_204_;
v___y_156_ = v___y_193_;
v___y_157_ = v_a_198_;
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
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_217_, v___y_215_);
lean_dec(v___y_217_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_188_ = v___y_213_;
v___y_189_ = v___y_220_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
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
v___y_189_ = v___y_220_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
v___y_195_ = v_val_222_;
goto v___jp_187_;
}
}
v___jp_223_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = l_Lean_replaceRef(v_ref_142_, v___y_229_);
v___x_232_ = l_Lean_Syntax_getPos_x3f(v_ref_231_, v___y_226_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_213_ = v___y_224_;
v___y_214_ = v___y_225_;
v___y_215_ = v___y_226_;
v___y_216_ = v___y_227_;
v___y_217_ = v_ref_231_;
v___y_218_ = v___y_228_;
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
v___y_215_ = v___y_226_;
v___y_216_ = v___y_227_;
v___y_217_ = v_ref_231_;
v___y_218_ = v___y_228_;
v___y_219_ = v___y_230_;
v___y_220_ = v_val_234_;
goto v___jp_212_;
}
}
v___jp_236_:
{
if (v___y_243_ == 0)
{
v___y_224_ = v___y_237_;
v___y_225_ = v___y_238_;
v___y_226_ = v___y_242_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_241_;
v___y_230_ = v_severity_144_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_237_;
v___y_225_ = v___y_238_;
v___y_226_ = v___y_242_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_241_;
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
v___y_237_ = v___f_253_;
v___y_238_ = v_fileMap_247_;
v___y_239_ = v_suppressElabErrors_250_;
v___y_240_ = v_fileName_246_;
v___y_241_ = v_ref_249_;
v___y_242_ = v___y_245_;
v___y_243_ = v___x_255_;
goto v___jp_236_;
}
else
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = l_Lean_warningAsError;
v___x_257_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_248_, v___x_256_);
v___y_237_ = v___f_253_;
v___y_238_ = v_fileMap_247_;
v___y_239_ = v_suppressElabErrors_250_;
v___y_240_ = v_fileName_246_;
v___y_241_ = v_ref_249_;
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
lean_object* v_name_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_333_; 
v_name_318_ = lean_ctor_get(v_linterOption_306_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_linterOption_306_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_linterOption_306_, 1);
lean_dec(v_unused_334_);
v___x_320_ = v_linterOption_306_;
v_isShared_321_ = v_isSharedCheck_333_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_name_318_);
lean_dec(v_linterOption_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_333_;
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
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_332_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_disable_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v_disable_328_ = l_Lean_MessageData_note(v___x_327_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v_msg_308_);
lean_ctor_set(v___x_329_, 1, v_disable_328_);
v___x_330_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_330_, 0, v_name_318_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_307_, v___x_330_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
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
lean_dec(v_stx_336_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v___x_353_; lean_object* v_toEnvExtension_354_; lean_object* v_asyncMode_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_linterSets_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_351_ = lean_st_ref_get(v___y_349_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref(v_env_352_);
lean_dec(v___x_351_);
v___x_353_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_354_ = lean_ctor_get(v___x_353_, 0);
v_asyncMode_355_ = lean_ctor_get(v_toEnvExtension_354_, 2);
v___x_356_ = lean_box(1);
v___x_357_ = lean_box(0);
v_linterSets_358_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_356_, v___x_353_, v_env_352_, v_asyncMode_355_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_o_348_);
lean_ctor_set(v___x_359_, 1, v_linterSets_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_361_, v___y_362_);
lean_dec(v___y_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_options_374_; lean_object* v___x_375_; 
v_options_374_ = lean_ctor_get(v___y_371_, 2);
lean_inc_ref(v_options_374_);
v___x_375_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_374_, v___y_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_386_, lean_object* v_stx_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v___x_398_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; 
v___x_403_ = l_Lean_Linter_getLinterValue(v_linterOption_386_, v_a_399_);
lean_dec(v_a_399_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_dec_ref(v_msg_388_);
lean_dec_ref(v_linterOption_386_);
v___x_404_ = lean_box(0);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v___x_408_; 
lean_del_object(v___x_401_);
v___x_408_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_386_, v_stx_387_, v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_410_, lean_object* v_stx_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_410_, v_stx_411_, v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_stx_411_);
return v_res_422_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_426_, lean_object* v_fvars_427_, lean_object* v_ids_428_, lean_object* v_a_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_a_441_; uint8_t v___x_445_; 
v___x_445_ = lean_nat_dec_lt(v_a_429_, v_upperBound_426_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec(v_a_429_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v_b_430_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_array_get_size(v_fvars_427_);
v___x_449_ = lean_nat_dec_lt(v_a_429_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_451_ = lean_array_fget_borrowed(v_ids_428_, v_a_429_);
v___x_452_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
v___x_453_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_450_, v___x_451_, v___x_452_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_dec_ref_known(v___x_453_, 1);
v_a_441_ = v___x_447_;
goto v___jp_440_;
}
else
{
lean_dec(v_a_429_);
return v___x_453_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_array_fget_borrowed(v_ids_428_, v_a_429_);
v___x_455_ = lean_array_fget_borrowed(v_fvars_427_, v_a_429_);
lean_inc(v___x_455_);
v___x_456_ = l_Lean_mkFVar(v___x_455_);
lean_inc(v___x_454_);
v___x_457_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_454_, v___x_456_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_dec_ref_known(v___x_457_, 1);
v_a_441_ = v___x_447_;
goto v___jp_440_;
}
else
{
lean_dec(v_a_429_);
return v___x_457_;
}
}
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_a_429_, v___x_442_);
lean_dec(v_a_429_);
v_a_429_ = v___x_443_;
v_b_430_ = v_a_441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_458_, lean_object* v_fvars_459_, lean_object* v_ids_460_, lean_object* v_a_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_458_, v_fvars_459_, v_ids_460_, v_a_461_, v_b_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_ids_460_);
lean_dec_ref(v_fvars_459_);
lean_dec(v_upperBound_458_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_473_, lean_object* v_fvars_474_, lean_object* v_ids_475_, lean_object* v___x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_473_, v_fvars_474_, v_ids_475_, v___x_486_, v___x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_495_);
v___x_489_ = v___x_487_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_dec(v___x_487_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_476_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_476_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_496_, lean_object* v_fvars_497_, lean_object* v_ids_498_, lean_object* v___x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_496_, v_fvars_497_, v_ids_498_, v___x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_ids_498_);
lean_dec_ref(v_fvars_497_);
lean_dec(v___x_496_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_510_, lean_object* v_fvars_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_524_; 
v___x_521_ = lean_array_get_size(v_ids_510_);
v___x_522_ = lean_box(0);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_523_, 0, v___x_521_);
lean_closure_set(v___f_523_, 1, v_fvars_511_);
lean_closure_set(v___f_523_, 2, v_ids_510_);
lean_closure_set(v___f_523_, 3, v___x_522_);
v___x_524_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_523_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_525_, lean_object* v_fvars_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_525_, v_fvars_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_537_, lean_object* v_fvars_538_, lean_object* v_ids_539_, lean_object* v_inst_540_, lean_object* v_R_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_c_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_537_, v_fvars_538_, v_ids_539_, v_a_542_, v_b_543_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_555_ = _args[0];
lean_object* v_fvars_556_ = _args[1];
lean_object* v_ids_557_ = _args[2];
lean_object* v_inst_558_ = _args[3];
lean_object* v_R_559_ = _args[4];
lean_object* v_a_560_ = _args[5];
lean_object* v_b_561_ = _args[6];
lean_object* v_c_562_ = _args[7];
lean_object* v___y_563_ = _args[8];
lean_object* v___y_564_ = _args[9];
lean_object* v___y_565_ = _args[10];
lean_object* v___y_566_ = _args[11];
lean_object* v___y_567_ = _args[12];
lean_object* v___y_568_ = _args[13];
lean_object* v___y_569_ = _args[14];
lean_object* v___y_570_ = _args[15];
lean_object* v___y_571_ = _args[16];
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_555_, v_fvars_556_, v_ids_557_, v_inst_558_, v_R_559_, v_a_560_, v_b_561_, v_c_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_ids_557_);
lean_dec_ref(v_fvars_556_);
lean_dec(v_upperBound_555_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_573_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_595_, lean_object* v_msgData_596_, uint8_t v_severity_597_, uint8_t v_isSilent_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_595_, v_msgData_596_, v_severity_597_, v_isSilent_598_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_609_, lean_object* v_msgData_610_, lean_object* v_severity_611_, lean_object* v_isSilent_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v_severity_boxed_622_; uint8_t v_isSilent_boxed_623_; lean_object* v_res_624_; 
v_severity_boxed_622_ = lean_unbox(v_severity_611_);
v_isSilent_boxed_623_ = lean_unbox(v_isSilent_612_);
v_res_624_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_609_, v_msgData_610_, v_severity_boxed_622_, v_isSilent_boxed_623_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_ref_609_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(lean_object* v_00_u03b1_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(v_00_u03b1_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 5);
v___x_654_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_ref_653_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_ref_653_);
lean_ctor_set(v___x_659_, 1, v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(lean_object* v_ctor_675_, lean_object* v_args_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_836_ = lean_string_dec_eq(v_ctor_675_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_array_get_size(v_args_676_);
v___x_839_ = lean_unsigned_to_nat(11u);
v___x_840_ = lean_nat_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v___x_841_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_842_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_841_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
goto v___jp_682_;
}
}
v___jp_682_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = l_Lean_instInhabitedExpr;
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_684_);
lean_inc(v___x_685_);
v___x_686_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_685_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_688_);
lean_inc(v___x_689_);
v___x_690_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_689_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_unsigned_to_nat(2u);
v___x_693_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_692_);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_693_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_unsigned_to_nat(3u);
v___x_697_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_696_);
lean_inc(v___x_697_);
v___x_698_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_697_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = lean_unsigned_to_nat(4u);
v___x_701_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_700_);
lean_inc(v___x_701_);
v___x_702_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_701_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_unsigned_to_nat(5u);
v___x_705_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_704_);
lean_inc(v___x_705_);
v___x_706_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_705_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = lean_unsigned_to_nat(6u);
v___x_709_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_708_);
lean_inc(v___x_709_);
v___x_710_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_709_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_unsigned_to_nat(7u);
v___x_713_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_712_);
lean_inc(v___x_713_);
v___x_714_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_713_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_unsigned_to_nat(8u);
v___x_717_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_716_);
lean_inc(v___x_717_);
v___x_718_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_717_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_unsigned_to_nat(9u);
v___x_721_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_720_);
lean_inc(v___x_721_);
v___x_722_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_721_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_unsigned_to_nat(10u);
v___x_725_ = lean_array_get_borrowed(v___x_683_, v_args_676_, v___x_724_);
lean_inc(v___x_725_);
v___x_726_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_725_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_746_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_746_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; uint8_t v___x_732_; uint8_t v___x_733_; uint8_t v___x_734_; uint8_t v___x_735_; uint8_t v___x_736_; uint8_t v___x_737_; uint8_t v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; lean_object* v___x_744_; 
v___x_731_ = lean_alloc_ctor(0, 0, 11);
v___x_732_ = lean_unbox(v_a_687_);
lean_dec(v_a_687_);
lean_ctor_set_uint8(v___x_731_, 0, v___x_732_);
v___x_733_ = lean_unbox(v_a_691_);
lean_dec(v_a_691_);
lean_ctor_set_uint8(v___x_731_, 1, v___x_733_);
v___x_734_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
lean_ctor_set_uint8(v___x_731_, 2, v___x_734_);
v___x_735_ = lean_unbox(v_a_699_);
lean_dec(v_a_699_);
lean_ctor_set_uint8(v___x_731_, 3, v___x_735_);
v___x_736_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
lean_ctor_set_uint8(v___x_731_, 4, v___x_736_);
v___x_737_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
lean_ctor_set_uint8(v___x_731_, 5, v___x_737_);
v___x_738_ = lean_unbox(v_a_711_);
lean_dec(v_a_711_);
lean_ctor_set_uint8(v___x_731_, 6, v___x_738_);
v___x_739_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
lean_ctor_set_uint8(v___x_731_, 7, v___x_739_);
v___x_740_ = lean_unbox(v_a_719_);
lean_dec(v_a_719_);
lean_ctor_set_uint8(v___x_731_, 8, v___x_740_);
v___x_741_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
lean_ctor_set_uint8(v___x_731_, 9, v___x_741_);
v___x_742_ = lean_unbox(v_a_727_);
lean_dec(v_a_727_);
lean_ctor_set_uint8(v___x_731_, 10, v___x_742_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_744_ = v___x_729_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_731_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_723_);
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_747_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_726_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_726_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_719_);
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_755_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_722_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_722_);
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
lean_dec(v_a_715_);
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_763_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_718_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_718_);
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
lean_dec(v_a_711_);
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_771_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_714_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_714_);
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
lean_dec(v_a_707_);
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_779_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_710_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_710_);
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
lean_dec(v_a_703_);
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_787_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_706_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_706_);
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
lean_dec(v_a_699_);
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_795_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_702_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_702_);
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
lean_dec(v_a_695_);
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_803_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_698_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_698_);
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
lean_dec(v_a_691_);
lean_dec(v_a_687_);
v_a_811_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_694_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_694_);
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
lean_dec(v_a_687_);
v_a_819_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_690_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_690_);
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
v_a_827_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_686_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_686_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_851_, lean_object* v_args_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(v_ctor_851_, v_args_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v_args_852_);
lean_dec_ref(v_ctor_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___f_872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0));
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_874_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_873_, v___f_872_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(lean_object* v_00_u03b1_882_, lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_890_, lean_object* v_msg_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(v_00_u03b1_890_, v_msg_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_901_ = l_Lean_Expr_const___override(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0));
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Expr_hasMVar(v_e_908_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_e_908_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v_mctx_914_; lean_object* v___x_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v_cache_919_; lean_object* v_zetaDeltaFVarIds_920_; lean_object* v_postponed_921_; lean_object* v_diag_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
v___x_913_ = lean_st_ref_get(v___y_909_);
v_mctx_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_mctx_914_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_instantiateMVarsCore(v_mctx_914_, v_e_908_);
v_fst_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v___x_915_, 1);
lean_inc(v_snd_917_);
lean_dec_ref(v___x_915_);
v___x_918_ = lean_st_ref_take(v___y_909_);
v_cache_919_ = lean_ctor_get(v___x_918_, 1);
v_zetaDeltaFVarIds_920_ = lean_ctor_get(v___x_918_, 2);
v_postponed_921_ = lean_ctor_get(v___x_918_, 3);
v_diag_922_ = lean_ctor_get(v___x_918_, 4);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_918_, 0);
lean_dec(v_unused_932_);
v___x_924_ = v___x_918_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_diag_922_);
lean_inc(v_postponed_921_);
lean_inc(v_zetaDeltaFVarIds_920_);
lean_inc(v_cache_919_);
lean_dec(v___x_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_snd_917_);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_snd_917_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_cache_919_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_zetaDeltaFVarIds_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_postponed_921_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_diag_922_);
v___x_927_ = v_reuseFailAlloc_930_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_st_ref_set(v___y_909_, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_fst_916_);
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_933_, v___y_934_);
lean_dec(v___y_934_);
return v_res_936_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_box(1);
v___x_938_ = l_Lean_MessageData_ofFormat(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2));
v___x_943_ = l_Lean_MessageData_ofFormat(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
return v_x_944_;
}
else
{
lean_object* v_head_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_969_; 
v_head_946_ = lean_ctor_get(v_x_945_, 0);
v_tail_947_ = lean_ctor_get(v_x_945_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_945_);
if (v_isSharedCheck_969_ == 0)
{
v___x_949_ = v_x_945_;
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_head_946_);
lean_dec(v_x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_before_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_967_; 
v_before_951_ = lean_ctor_get(v_head_946_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_head_946_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_head_946_, 1);
lean_dec(v_unused_968_);
v___x_953_ = v_head_946_;
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_before_951_);
lean_dec(v_head_946_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 7);
lean_ctor_set(v___x_953_, 1, v___x_955_);
lean_ctor_set(v___x_953_, 0, v_x_944_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_x_944_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_966_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 7);
lean_ctor_set(v___x_949_, 1, v___x_958_);
lean_ctor_set(v___x_949_, 0, v___x_957_);
v___x_960_ = v___x_949_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = l_Lean_MessageData_ofSyntax(v_before_951_);
v___x_962_ = l_Lean_indentD(v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v_x_944_ = v___x_963_;
v_x_945_ = v_tail_947_;
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
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_974_ = l_Lean_MessageData_ofFormat(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_975_, lean_object* v_macroStack_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_options_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_options_979_ = lean_ctor_get(v___y_977_, 2);
v___x_980_ = l_Lean_Elab_pp_macroStack;
v___x_981_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec(v_macroStack_976_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_msgData_975_);
return v___x_982_;
}
else
{
if (lean_obj_tag(v_macroStack_976_) == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_msgData_975_);
return v___x_983_;
}
else
{
lean_object* v_head_984_; lean_object* v_after_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1000_; 
v_head_984_ = lean_ctor_get(v_macroStack_976_, 0);
lean_inc(v_head_984_);
v_after_985_ = lean_ctor_get(v_head_984_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_head_984_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_head_984_, 0);
lean_dec(v_unused_1001_);
v___x_987_ = v_head_984_;
v_isShared_988_ = v_isSharedCheck_1000_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_after_985_);
lean_dec(v_head_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1000_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 7);
lean_ctor_set(v___x_987_, 1, v___x_989_);
lean_ctor_set(v___x_987_, 0, v_msgData_975_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_msgData_975_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_999_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_msgData_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_992_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_MessageData_ofSyntax(v_after_985_);
v___x_995_ = l_Lean_indentD(v___x_994_);
v_msgData_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_996_, 0, v___x_993_);
lean_ctor_set(v_msgData_996_, 1, v___x_995_);
v___x_997_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_msgData_996_, v_macroStack_976_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1002_, lean_object* v_macroStack_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1002_, v_macroStack_1003_, v___y_1004_);
lean_dec_ref(v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_ref_1015_; lean_object* v___x_1016_; lean_object* v_a_1017_; lean_object* v_macroStack_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_ref_1015_ = lean_ctor_get(v___y_1012_, 5);
v___x_1016_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1007_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v_macroStack_1018_ = lean_ctor_get(v___y_1008_, 1);
v___x_1019_ = l_Lean_Elab_getBetterRef(v_ref_1015_, v_macroStack_1018_);
lean_inc(v_macroStack_1018_);
v___x_1020_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_1017_, v_macroStack_1018_, v___y_1012_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1019_);
lean_ctor_set(v___x_1025_, 1, v_a_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_Elab_abortTermExceptionId;
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_1046_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0));
v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
v___x_1051_ = l_Lean_MessageData_ofExpr(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_1053_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_1059_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_ty_x3f_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_fileName_1081_; lean_object* v_fileMap_1082_; lean_object* v_options_1083_; lean_object* v_currRecDepth_1084_; lean_object* v_maxRecDepth_1085_; lean_object* v_ref_1086_; lean_object* v_currNamespace_1087_; lean_object* v_openDecls_1088_; lean_object* v_initHeartbeats_1089_; lean_object* v_maxHeartbeats_1090_; lean_object* v_quotContext_1091_; lean_object* v_currMacroScope_1092_; uint8_t v_diag_1093_; lean_object* v_cancelTk_x3f_1094_; uint8_t v_suppressElabErrors_1095_; lean_object* v_inheritedTraceOptions_1096_; uint8_t v___x_1097_; lean_object* v_ref_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_ty_x3f_1075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
v___x_1076_ = 1;
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_box(v___x_1076_);
v___x_1079_ = lean_box(v___x_1076_);
lean_inc(v_stx_1067_);
v___x_1080_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1080_, 0, v_stx_1067_);
lean_closure_set(v___x_1080_, 1, v_ty_x3f_1075_);
lean_closure_set(v___x_1080_, 2, v___x_1078_);
lean_closure_set(v___x_1080_, 3, v___x_1079_);
lean_closure_set(v___x_1080_, 4, v___x_1077_);
v_fileName_1081_ = lean_ctor_get(v_a_1072_, 0);
v_fileMap_1082_ = lean_ctor_get(v_a_1072_, 1);
v_options_1083_ = lean_ctor_get(v_a_1072_, 2);
v_currRecDepth_1084_ = lean_ctor_get(v_a_1072_, 3);
v_maxRecDepth_1085_ = lean_ctor_get(v_a_1072_, 4);
v_ref_1086_ = lean_ctor_get(v_a_1072_, 5);
v_currNamespace_1087_ = lean_ctor_get(v_a_1072_, 6);
v_openDecls_1088_ = lean_ctor_get(v_a_1072_, 7);
v_initHeartbeats_1089_ = lean_ctor_get(v_a_1072_, 8);
v_maxHeartbeats_1090_ = lean_ctor_get(v_a_1072_, 9);
v_quotContext_1091_ = lean_ctor_get(v_a_1072_, 10);
v_currMacroScope_1092_ = lean_ctor_get(v_a_1072_, 11);
v_diag_1093_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*14);
v_cancelTk_x3f_1094_ = lean_ctor_get(v_a_1072_, 12);
v_suppressElabErrors_1095_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1096_ = lean_ctor_get(v_a_1072_, 13);
v___x_1097_ = 1;
v_ref_1098_ = l_Lean_replaceRef(v_stx_1067_, v_ref_1086_);
lean_dec(v_stx_1067_);
lean_inc_ref(v_inheritedTraceOptions_1096_);
lean_inc(v_cancelTk_x3f_1094_);
lean_inc(v_currMacroScope_1092_);
lean_inc(v_quotContext_1091_);
lean_inc(v_maxHeartbeats_1090_);
lean_inc(v_initHeartbeats_1089_);
lean_inc(v_openDecls_1088_);
lean_inc(v_currNamespace_1087_);
lean_inc(v_maxRecDepth_1085_);
lean_inc(v_currRecDepth_1084_);
lean_inc_ref(v_options_1083_);
lean_inc_ref(v_fileMap_1082_);
lean_inc_ref(v_fileName_1081_);
v___x_1099_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1099_, 0, v_fileName_1081_);
lean_ctor_set(v___x_1099_, 1, v_fileMap_1082_);
lean_ctor_set(v___x_1099_, 2, v_options_1083_);
lean_ctor_set(v___x_1099_, 3, v_currRecDepth_1084_);
lean_ctor_set(v___x_1099_, 4, v_maxRecDepth_1085_);
lean_ctor_set(v___x_1099_, 5, v_ref_1098_);
lean_ctor_set(v___x_1099_, 6, v_currNamespace_1087_);
lean_ctor_set(v___x_1099_, 7, v_openDecls_1088_);
lean_ctor_set(v___x_1099_, 8, v_initHeartbeats_1089_);
lean_ctor_set(v___x_1099_, 9, v_maxHeartbeats_1090_);
lean_ctor_set(v___x_1099_, 10, v_quotContext_1091_);
lean_ctor_set(v___x_1099_, 11, v_currMacroScope_1092_);
lean_ctor_set(v___x_1099_, 12, v_cancelTk_x3f_1094_);
lean_ctor_set(v___x_1099_, 13, v_inheritedTraceOptions_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*14, v_diag_1093_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*14 + 1, v_suppressElabErrors_1095_);
v___x_1100_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1080_, v___x_1097_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v___x_1099_, v_a_1073_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v_a_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___x_1198_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_1101_, v_a_1071_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1198_ = l_Lean_Expr_hasSorry(v_a_1103_);
if (v___x_1198_ == 0)
{
v___y_1143_ = v_a_1068_;
v___y_1144_ = v_a_1069_;
v___y_1145_ = v_a_1070_;
v___y_1146_ = v_a_1071_;
v___y_1147_ = v___x_1099_;
v___y_1148_ = v_a_1073_;
goto v___jp_1142_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = l_Lean_Expr_hasSyntheticSorry(v_a_1103_);
if (v___x_1199_ == 0)
{
v___y_1180_ = v_a_1068_;
v___y_1181_ = v_a_1069_;
v___y_1182_ = v_a_1070_;
v___y_1183_ = v_a_1071_;
v___y_1184_ = v___x_1099_;
v___y_1185_ = v_a_1073_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_a_1103_);
lean_dec_ref_known(v___x_1099_, 14);
v___x_1200_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
v___jp_1104_:
{
if (v___y_1114_ == 0)
{
if (lean_obj_tag(v___y_1105_) == 0)
{
lean_dec_ref_known(v___y_1105_, 2);
lean_dec_ref(v___y_1113_);
lean_dec(v_a_1103_);
return v___y_1108_;
}
else
{
lean_object* v_id_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1128_; 
v_id_1115_ = lean_ctor_get(v___y_1105_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___y_1105_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___y_1105_, 1);
lean_dec(v_unused_1129_);
v___x_1117_ = v___y_1105_;
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_id_1115_);
lean_dec(v___y_1105_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1112_, v_id_1115_);
lean_dec(v_id_1115_);
if (v___x_1119_ == 0)
{
lean_del_object(v___x_1117_);
lean_dec_ref(v___y_1113_);
lean_dec(v_a_1103_);
return v___y_1108_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_dec_ref(v___y_1108_);
v___x_1120_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6);
v___x_1121_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_1122_ = l_Lean_indentExpr(v_a_1103_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 7);
lean_ctor_set(v___x_1117_, 1, v___x_1122_);
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1124_ = v___x_1117_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___x_1120_);
v___x_1126_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1125_, v___y_1106_, v___y_1110_, v___y_1109_, v___y_1107_, v___y_1113_, v___y_1111_);
lean_dec_ref(v___y_1113_);
return v___x_1126_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1105_);
lean_dec(v_a_1103_);
return v___y_1108_;
}
}
v___jp_1130_:
{
lean_object* v___x_1137_; 
lean_inc(v_a_1103_);
v___x_1137_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_1103_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_dec_ref(v___y_1135_);
lean_dec(v_a_1103_);
return v___x_1137_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
v___x_1139_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1140_ = l_Lean_Exception_isInterrupt(v_a_1138_);
if (v___x_1140_ == 0)
{
uint8_t v___x_1141_; 
lean_inc(v_a_1138_);
v___x_1141_ = l_Lean_Exception_isRuntime(v_a_1138_);
v___y_1105_ = v_a_1138_;
v___y_1106_ = v___y_1131_;
v___y_1107_ = v___y_1134_;
v___y_1108_ = v___x_1137_;
v___y_1109_ = v___y_1133_;
v___y_1110_ = v___y_1132_;
v___y_1111_ = v___y_1136_;
v___y_1112_ = v___x_1139_;
v___y_1113_ = v___y_1135_;
v___y_1114_ = v___x_1141_;
goto v___jp_1104_;
}
else
{
v___y_1105_ = v_a_1138_;
v___y_1106_ = v___y_1131_;
v___y_1107_ = v___y_1134_;
v___y_1108_ = v___x_1137_;
v___y_1109_ = v___y_1133_;
v___y_1110_ = v___y_1132_;
v___y_1111_ = v___y_1136_;
v___y_1112_ = v___x_1139_;
v___y_1113_ = v___y_1135_;
v___y_1114_ = v___x_1140_;
goto v___jp_1104_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1149_; 
lean_inc(v_a_1103_);
v___x_1149_ = l_Lean_Meta_getMVars(v_a_1103_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1150_, v___x_1077_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v_a_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; uint8_t v___x_1153_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = lean_unbox(v_a_1152_);
lean_dec(v_a_1152_);
if (v___x_1153_ == 0)
{
v___y_1131_ = v___y_1143_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1145_;
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1147_;
v___y_1136_ = v___y_1148_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___y_1147_);
lean_dec(v_a_1103_);
v___x_1154_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
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
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___y_1147_);
lean_dec(v_a_1103_);
v_a_1163_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1151_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1151_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___y_1147_);
lean_dec(v_a_1103_);
v_a_1171_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1149_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1149_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
v___jp_1179_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v___x_1186_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_1187_ = l_Lean_indentExpr(v_a_1103_);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_1188_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1184_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref_known(v___x_1099_, 14);
v_a_1209_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1100_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1100_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_stx_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(lean_object* v_config_1295_, lean_object* v_item_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_item_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1315_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1296_, v___x_1314_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1315_) == 0)
{
uint8_t v___x_1316_; 
lean_dec_ref_known(v___x_1315_, 1);
v___x_1316_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1296_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1317_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1296_);
lean_inc_ref(v_item_1296_);
v___x_1318_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1296_);
v___x_1319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_1320_ = lean_string_dec_lt(v___x_1317_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_1322_ = lean_string_dec_lt(v___x_1317_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_string_dec_eq(v___x_1317_, v___x_1321_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_1325_ = lean_string_dec_eq(v___x_1317_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_1327_ = lean_string_dec_eq(v___x_1317_, v___x_1326_);
lean_dec_ref(v___x_1317_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_1329_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1328_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1329_) == 0)
{
uint8_t v___x_1330_; 
lean_dec_ref_known(v___x_1329_, 1);
v___x_1330_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1330_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v___x_1318_);
v___x_1331_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1357_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1357_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1357_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
uint8_t v_proofs_1336_; uint8_t v_types_1337_; uint8_t v_implicits_1338_; uint8_t v_descend_1339_; uint8_t v_underBinder_1340_; uint8_t v_merge_1341_; uint8_t v_useContext_1342_; uint8_t v_onlyGivenNames_1343_; uint8_t v_preserveBinderNames_1344_; uint8_t v_lift_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1356_; 
v_proofs_1336_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1337_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1338_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1339_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1340_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_merge_1341_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1342_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1343_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1344_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1345_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1347_ = v_config_1295_;
v_isShared_1348_ = v_isSharedCheck_1356_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v_config_1295_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1356_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, 0, v_proofs_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, 1, v_types_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, 2, v_implicits_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, 3, v_descend_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1355_, 4, v_underBinder_1340_);
v___x_1350_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
uint8_t v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unbox(v_a_1332_);
lean_dec(v_a_1332_);
lean_ctor_set_uint8(v___x_1350_, 5, v___x_1351_);
lean_ctor_set_uint8(v___x_1350_, 6, v_merge_1341_);
lean_ctor_set_uint8(v___x_1350_, 7, v_useContext_1342_);
lean_ctor_set_uint8(v___x_1350_, 8, v_onlyGivenNames_1343_);
lean_ctor_set_uint8(v___x_1350_, 9, v_preserveBinderNames_1344_);
lean_ctor_set_uint8(v___x_1350_, 10, v_lift_1345_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1350_);
v___x_1353_ = v___x_1334_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1350_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_config_1295_);
v_a_1358_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1331_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1331_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
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
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1366_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1329_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1329_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v___x_1317_);
v___x_1374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_1375_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1374_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1375_) == 0)
{
uint8_t v___x_1376_; 
lean_dec_ref_known(v___x_1375_, 1);
v___x_1376_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1376_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref(v___x_1318_);
v___x_1377_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1403_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1403_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1403_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
uint8_t v_proofs_1382_; uint8_t v_types_1383_; uint8_t v_implicits_1384_; uint8_t v_descend_1385_; uint8_t v_underBinder_1386_; uint8_t v_usedOnly_1387_; uint8_t v_merge_1388_; uint8_t v_onlyGivenNames_1389_; uint8_t v_preserveBinderNames_1390_; uint8_t v_lift_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1402_; 
v_proofs_1382_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1383_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1384_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1385_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1386_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1387_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1388_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_onlyGivenNames_1389_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1390_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1391_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1393_ = v_config_1295_;
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_config_1295_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 0, v_proofs_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 1, v_types_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 2, v_implicits_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 3, v_descend_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 4, v_underBinder_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 5, v_usedOnly_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, 6, v_merge_1388_);
v___x_1396_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
uint8_t v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
lean_ctor_set_uint8(v___x_1396_, 7, v___x_1397_);
lean_ctor_set_uint8(v___x_1396_, 8, v_onlyGivenNames_1389_);
lean_ctor_set_uint8(v___x_1396_, 9, v_preserveBinderNames_1390_);
lean_ctor_set_uint8(v___x_1396_, 10, v_lift_1391_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1396_);
v___x_1399_ = v___x_1380_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1396_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_config_1295_);
v_a_1404_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1377_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1377_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
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
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1412_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1375_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1375_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec_ref(v___x_1317_);
v___x_1420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_1421_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1420_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1421_) == 0)
{
uint8_t v___x_1422_; 
lean_dec_ref_known(v___x_1421_, 1);
v___x_1422_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1422_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1423_; 
lean_dec_ref(v___x_1318_);
v___x_1423_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1449_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1449_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1449_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
uint8_t v_proofs_1428_; uint8_t v_types_1429_; uint8_t v_implicits_1430_; uint8_t v_descend_1431_; uint8_t v_usedOnly_1432_; uint8_t v_merge_1433_; uint8_t v_useContext_1434_; uint8_t v_onlyGivenNames_1435_; uint8_t v_preserveBinderNames_1436_; uint8_t v_lift_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1448_; 
v_proofs_1428_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1429_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1430_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1431_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_usedOnly_1432_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1433_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1434_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1435_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1436_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1437_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1439_ = v_config_1295_;
v_isShared_1440_ = v_isSharedCheck_1448_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_config_1295_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1448_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, 0, v_proofs_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, 1, v_types_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, 2, v_implicits_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, 3, v_descend_1431_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
uint8_t v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
lean_ctor_set_uint8(v___x_1442_, 4, v___x_1443_);
lean_ctor_set_uint8(v___x_1442_, 5, v_usedOnly_1432_);
lean_ctor_set_uint8(v___x_1442_, 6, v_merge_1433_);
lean_ctor_set_uint8(v___x_1442_, 7, v_useContext_1434_);
lean_ctor_set_uint8(v___x_1442_, 8, v_onlyGivenNames_1435_);
lean_ctor_set_uint8(v___x_1442_, 9, v_preserveBinderNames_1436_);
lean_ctor_set_uint8(v___x_1442_, 10, v_lift_1437_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1442_);
v___x_1445_ = v___x_1426_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1442_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_config_1295_);
v_a_1450_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1423_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1423_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
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
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1458_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1421_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1421_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_string_dec_eq(v___x_1317_, v___x_1319_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_1468_ = lean_string_dec_eq(v___x_1317_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_1470_ = lean_string_dec_eq(v___x_1317_, v___x_1469_);
lean_dec_ref(v___x_1317_);
if (v___x_1470_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_1472_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1471_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1472_) == 0)
{
uint8_t v___x_1473_; 
lean_dec_ref_known(v___x_1472_, 1);
v___x_1473_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1474_; 
lean_dec_ref(v___x_1318_);
v___x_1474_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1500_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1500_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1500_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
uint8_t v_proofs_1479_; uint8_t v_implicits_1480_; uint8_t v_descend_1481_; uint8_t v_underBinder_1482_; uint8_t v_usedOnly_1483_; uint8_t v_merge_1484_; uint8_t v_useContext_1485_; uint8_t v_onlyGivenNames_1486_; uint8_t v_preserveBinderNames_1487_; uint8_t v_lift_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1499_; 
v_proofs_1479_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_implicits_1480_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1481_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1482_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1483_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1484_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1485_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1486_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1487_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1488_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1490_ = v_config_1295_;
v_isShared_1491_ = v_isSharedCheck_1499_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v_config_1295_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1499_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1498_, 0, v_proofs_1479_);
v___x_1493_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
uint8_t v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unbox(v_a_1475_);
lean_dec(v_a_1475_);
lean_ctor_set_uint8(v___x_1493_, 1, v___x_1494_);
lean_ctor_set_uint8(v___x_1493_, 2, v_implicits_1480_);
lean_ctor_set_uint8(v___x_1493_, 3, v_descend_1481_);
lean_ctor_set_uint8(v___x_1493_, 4, v_underBinder_1482_);
lean_ctor_set_uint8(v___x_1493_, 5, v_usedOnly_1483_);
lean_ctor_set_uint8(v___x_1493_, 6, v_merge_1484_);
lean_ctor_set_uint8(v___x_1493_, 7, v_useContext_1485_);
lean_ctor_set_uint8(v___x_1493_, 8, v_onlyGivenNames_1486_);
lean_ctor_set_uint8(v___x_1493_, 9, v_preserveBinderNames_1487_);
lean_ctor_set_uint8(v___x_1493_, 10, v_lift_1488_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1496_ = v___x_1477_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1493_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_config_1295_);
v_a_1501_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1474_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1474_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
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
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1509_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1472_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1472_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v___x_1317_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_1518_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1517_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1518_) == 0)
{
uint8_t v___x_1519_; 
lean_dec_ref_known(v___x_1518_, 1);
v___x_1519_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v___x_1318_);
v___x_1520_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1546_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1546_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1546_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v_types_1525_; uint8_t v_implicits_1526_; uint8_t v_descend_1527_; uint8_t v_underBinder_1528_; uint8_t v_usedOnly_1529_; uint8_t v_merge_1530_; uint8_t v_useContext_1531_; uint8_t v_onlyGivenNames_1532_; uint8_t v_preserveBinderNames_1533_; uint8_t v_lift_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1545_; 
v_types_1525_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1526_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1527_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1528_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1529_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1530_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1531_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1532_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1533_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1534_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1536_ = v_config_1295_;
v_isShared_1537_ = v_isSharedCheck_1545_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_config_1295_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1545_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 0, 11);
v___x_1539_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
uint8_t v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_unbox(v_a_1521_);
lean_dec(v_a_1521_);
lean_ctor_set_uint8(v___x_1539_, 0, v___x_1540_);
lean_ctor_set_uint8(v___x_1539_, 1, v_types_1525_);
lean_ctor_set_uint8(v___x_1539_, 2, v_implicits_1526_);
lean_ctor_set_uint8(v___x_1539_, 3, v_descend_1527_);
lean_ctor_set_uint8(v___x_1539_, 4, v_underBinder_1528_);
lean_ctor_set_uint8(v___x_1539_, 5, v_usedOnly_1529_);
lean_ctor_set_uint8(v___x_1539_, 6, v_merge_1530_);
lean_ctor_set_uint8(v___x_1539_, 7, v_useContext_1531_);
lean_ctor_set_uint8(v___x_1539_, 8, v_onlyGivenNames_1532_);
lean_ctor_set_uint8(v___x_1539_, 9, v_preserveBinderNames_1533_);
lean_ctor_set_uint8(v___x_1539_, 10, v_lift_1534_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1539_);
v___x_1542_ = v___x_1523_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1539_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_config_1295_);
v_a_1547_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1520_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1520_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
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
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1555_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1518_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1518_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v___x_1317_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_1564_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1563_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1564_) == 0)
{
uint8_t v___x_1565_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1565_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1565_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v___x_1318_);
v___x_1566_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1592_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1592_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1592_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v_proofs_1571_; uint8_t v_types_1572_; uint8_t v_implicits_1573_; uint8_t v_descend_1574_; uint8_t v_underBinder_1575_; uint8_t v_usedOnly_1576_; uint8_t v_merge_1577_; uint8_t v_useContext_1578_; uint8_t v_onlyGivenNames_1579_; uint8_t v_lift_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1591_; 
v_proofs_1571_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1572_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1573_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1574_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1575_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1576_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1577_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1578_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1579_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_lift_1580_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1582_ = v_config_1295_;
v_isShared_1583_ = v_isSharedCheck_1591_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_config_1295_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1591_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 0, v_proofs_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 1, v_types_1572_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 2, v_implicits_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 3, v_descend_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 4, v_underBinder_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 5, v_usedOnly_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 6, v_merge_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 7, v_useContext_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, 8, v_onlyGivenNames_1579_);
v___x_1585_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
uint8_t v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_unbox(v_a_1567_);
lean_dec(v_a_1567_);
lean_ctor_set_uint8(v___x_1585_, 9, v___x_1586_);
lean_ctor_set_uint8(v___x_1585_, 10, v_lift_1580_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1585_);
v___x_1588_ = v___x_1569_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1585_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_config_1295_);
v_a_1593_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1566_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1566_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
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
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1601_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1564_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1564_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_1610_ = lean_string_dec_lt(v___x_1317_, v___x_1609_);
if (v___x_1610_ == 0)
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_string_dec_eq(v___x_1317_, v___x_1609_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_1613_ = lean_string_dec_eq(v___x_1317_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_1615_ = lean_string_dec_eq(v___x_1317_, v___x_1614_);
lean_dec_ref(v___x_1317_);
if (v___x_1615_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_1617_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1616_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1617_) == 0)
{
uint8_t v___x_1618_; 
lean_dec_ref_known(v___x_1617_, 1);
v___x_1618_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1619_; 
lean_dec_ref(v___x_1318_);
v___x_1619_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1645_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1645_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1645_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
uint8_t v_proofs_1624_; uint8_t v_types_1625_; uint8_t v_implicits_1626_; uint8_t v_descend_1627_; uint8_t v_underBinder_1628_; uint8_t v_usedOnly_1629_; uint8_t v_merge_1630_; uint8_t v_useContext_1631_; uint8_t v_preserveBinderNames_1632_; uint8_t v_lift_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1644_; 
v_proofs_1624_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1625_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1626_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1627_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1628_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1629_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1630_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1631_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_preserveBinderNames_1632_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1633_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1635_ = v_config_1295_;
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_config_1295_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 0, v_proofs_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 1, v_types_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 2, v_implicits_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 3, v_descend_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 4, v_underBinder_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 5, v_usedOnly_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 6, v_merge_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, 7, v_useContext_1631_);
v___x_1638_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
uint8_t v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
lean_ctor_set_uint8(v___x_1638_, 8, v___x_1639_);
lean_ctor_set_uint8(v___x_1638_, 9, v_preserveBinderNames_1632_);
lean_ctor_set_uint8(v___x_1638_, 10, v_lift_1633_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1638_);
v___x_1641_ = v___x_1622_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1638_);
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
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_config_1295_);
v_a_1646_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1619_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1619_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
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
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1654_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1617_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1617_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v___x_1317_);
v___x_1662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_1663_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1662_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1663_) == 0)
{
uint8_t v___x_1664_; 
lean_dec_ref_known(v___x_1663_, 1);
v___x_1664_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1665_; 
lean_dec_ref(v___x_1318_);
v___x_1665_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1691_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v_proofs_1670_; uint8_t v_types_1671_; uint8_t v_implicits_1672_; uint8_t v_descend_1673_; uint8_t v_underBinder_1674_; uint8_t v_usedOnly_1675_; uint8_t v_useContext_1676_; uint8_t v_onlyGivenNames_1677_; uint8_t v_preserveBinderNames_1678_; uint8_t v_lift_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1690_; 
v_proofs_1670_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1671_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1672_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1673_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1674_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1675_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_useContext_1676_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1677_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1678_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1679_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1681_ = v_config_1295_;
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
else
{
lean_dec(v_config_1295_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 0, v_proofs_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 1, v_types_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 2, v_implicits_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 3, v_descend_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 4, v_underBinder_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1689_, 5, v_usedOnly_1675_);
v___x_1684_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
uint8_t v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_unbox(v_a_1666_);
lean_dec(v_a_1666_);
lean_ctor_set_uint8(v___x_1684_, 6, v___x_1685_);
lean_ctor_set_uint8(v___x_1684_, 7, v_useContext_1676_);
lean_ctor_set_uint8(v___x_1684_, 8, v_onlyGivenNames_1677_);
lean_ctor_set_uint8(v___x_1684_, 9, v_preserveBinderNames_1678_);
lean_ctor_set_uint8(v___x_1684_, 10, v_lift_1679_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1684_);
v___x_1687_ = v___x_1668_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v_config_1295_);
v_a_1692_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1665_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1665_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
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
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1700_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1663_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1663_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v___x_1317_);
v___x_1708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_1709_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1708_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1709_) == 0)
{
uint8_t v___x_1710_; 
lean_dec_ref_known(v___x_1709_, 1);
v___x_1710_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1710_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v___x_1318_);
v___x_1711_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1737_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1737_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1737_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint8_t v_proofs_1716_; uint8_t v_types_1717_; uint8_t v_implicits_1718_; uint8_t v_descend_1719_; uint8_t v_underBinder_1720_; uint8_t v_usedOnly_1721_; uint8_t v_merge_1722_; uint8_t v_useContext_1723_; uint8_t v_onlyGivenNames_1724_; uint8_t v_preserveBinderNames_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1736_; 
v_proofs_1716_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1717_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1718_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_descend_1719_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1720_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1721_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1722_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1723_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1724_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1725_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1727_ = v_config_1295_;
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v_config_1295_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 0, v_proofs_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 1, v_types_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 2, v_implicits_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 3, v_descend_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 4, v_underBinder_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 5, v_usedOnly_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 6, v_merge_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 7, v_useContext_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 8, v_onlyGivenNames_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, 9, v_preserveBinderNames_1725_);
v___x_1730_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
uint8_t v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = lean_unbox(v_a_1712_);
lean_dec(v_a_1712_);
lean_ctor_set_uint8(v___x_1730_, 10, v___x_1731_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1730_);
v___x_1733_ = v___x_1714_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1730_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_config_1295_);
v_a_1738_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1711_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1711_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
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
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1746_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1709_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1709_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_1755_ = lean_string_dec_eq(v___x_1317_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_1757_ = lean_string_dec_eq(v___x_1317_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_1759_ = lean_string_dec_eq(v___x_1317_, v___x_1758_);
lean_dec_ref(v___x_1317_);
if (v___x_1759_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_1761_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1760_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1761_) == 0)
{
uint8_t v___x_1762_; 
lean_dec_ref_known(v___x_1761_, 1);
v___x_1762_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1762_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1763_; 
lean_dec_ref(v___x_1318_);
v___x_1763_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1789_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint8_t v_proofs_1768_; uint8_t v_types_1769_; uint8_t v_descend_1770_; uint8_t v_underBinder_1771_; uint8_t v_usedOnly_1772_; uint8_t v_merge_1773_; uint8_t v_useContext_1774_; uint8_t v_onlyGivenNames_1775_; uint8_t v_preserveBinderNames_1776_; uint8_t v_lift_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1788_; 
v_proofs_1768_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1769_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_descend_1770_ = lean_ctor_get_uint8(v_config_1295_, 3);
v_underBinder_1771_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1772_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1773_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1774_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1775_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1776_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1777_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1779_ = v_config_1295_;
v_isShared_1780_ = v_isSharedCheck_1788_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v_config_1295_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1788_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1787_, 0, v_proofs_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1787_, 1, v_types_1769_);
v___x_1782_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
uint8_t v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_unbox(v_a_1764_);
lean_dec(v_a_1764_);
lean_ctor_set_uint8(v___x_1782_, 2, v___x_1783_);
lean_ctor_set_uint8(v___x_1782_, 3, v_descend_1770_);
lean_ctor_set_uint8(v___x_1782_, 4, v_underBinder_1771_);
lean_ctor_set_uint8(v___x_1782_, 5, v_usedOnly_1772_);
lean_ctor_set_uint8(v___x_1782_, 6, v_merge_1773_);
lean_ctor_set_uint8(v___x_1782_, 7, v_useContext_1774_);
lean_ctor_set_uint8(v___x_1782_, 8, v_onlyGivenNames_1775_);
lean_ctor_set_uint8(v___x_1782_, 9, v_preserveBinderNames_1776_);
lean_ctor_set_uint8(v___x_1782_, 10, v_lift_1777_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1782_);
v___x_1785_ = v___x_1766_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1782_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_config_1295_);
v_a_1790_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1763_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1763_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
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
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1798_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1761_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1761_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec_ref(v___x_1317_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_1807_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1296_, v___x_1806_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1807_) == 0)
{
uint8_t v___x_1808_; 
lean_dec_ref_known(v___x_1807_, 1);
v___x_1808_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1809_; 
lean_dec_ref(v___x_1318_);
v___x_1809_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1835_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1835_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1835_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
uint8_t v_proofs_1814_; uint8_t v_types_1815_; uint8_t v_implicits_1816_; uint8_t v_underBinder_1817_; uint8_t v_usedOnly_1818_; uint8_t v_merge_1819_; uint8_t v_useContext_1820_; uint8_t v_onlyGivenNames_1821_; uint8_t v_preserveBinderNames_1822_; uint8_t v_lift_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1834_; 
v_proofs_1814_ = lean_ctor_get_uint8(v_config_1295_, 0);
v_types_1815_ = lean_ctor_get_uint8(v_config_1295_, 1);
v_implicits_1816_ = lean_ctor_get_uint8(v_config_1295_, 2);
v_underBinder_1817_ = lean_ctor_get_uint8(v_config_1295_, 4);
v_usedOnly_1818_ = lean_ctor_get_uint8(v_config_1295_, 5);
v_merge_1819_ = lean_ctor_get_uint8(v_config_1295_, 6);
v_useContext_1820_ = lean_ctor_get_uint8(v_config_1295_, 7);
v_onlyGivenNames_1821_ = lean_ctor_get_uint8(v_config_1295_, 8);
v_preserveBinderNames_1822_ = lean_ctor_get_uint8(v_config_1295_, 9);
v_lift_1823_ = lean_ctor_get_uint8(v_config_1295_, 10);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_config_1295_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1825_ = v_config_1295_;
v_isShared_1826_ = v_isSharedCheck_1834_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v_config_1295_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1834_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, 0, v_proofs_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, 1, v_types_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, 2, v_implicits_1816_);
v___x_1828_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
uint8_t v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = lean_unbox(v_a_1810_);
lean_dec(v_a_1810_);
lean_ctor_set_uint8(v___x_1828_, 3, v___x_1829_);
lean_ctor_set_uint8(v___x_1828_, 4, v_underBinder_1817_);
lean_ctor_set_uint8(v___x_1828_, 5, v_usedOnly_1818_);
lean_ctor_set_uint8(v___x_1828_, 6, v_merge_1819_);
lean_ctor_set_uint8(v___x_1828_, 7, v_useContext_1820_);
lean_ctor_set_uint8(v___x_1828_, 8, v_onlyGivenNames_1821_);
lean_ctor_set_uint8(v___x_1828_, 9, v_preserveBinderNames_1822_);
lean_ctor_set_uint8(v___x_1828_, 10, v_lift_1823_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1828_);
v___x_1831_ = v___x_1812_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1828_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_config_1295_);
v_a_1836_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1809_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1809_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
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
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1844_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1807_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1807_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
else
{
uint8_t v___x_1852_; 
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_config_1295_);
v___x_1852_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1318_);
if (v___x_1852_ == 0)
{
lean_dec_ref(v_item_1296_);
v_item_1305_ = v___x_1318_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
else
{
lean_object* v_value_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v___x_1318_);
v_value_1853_ = lean_ctor_get(v_item_1296_, 2);
lean_inc(v_value_1853_);
lean_dec_ref(v_item_1296_);
v___x_1854_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_value_1853_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1854_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_1295_);
v_item_1305_ = v_item_1296_;
v___y_1306_ = v___y_1297_;
v___y_1307_ = v___y_1298_;
v___y_1308_ = v___y_1299_;
v___y_1309_ = v___y_1300_;
v___y_1310_ = v___y_1301_;
v___y_1311_ = v___y_1302_;
goto v___jp_1304_;
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_item_1296_);
lean_dec_ref(v_config_1295_);
v_a_1855_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1315_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1315_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_1313_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1305_, v___x_1312_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1863_, lean_object* v_item_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(v_config_1863_, v_item_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_1875_, v___y_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(v_e_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_1921_, v_msg_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_1931_, lean_object* v_macroStack_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_1931_, v_macroStack_1932_, v___y_1937_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1941_, lean_object* v_macroStack_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_1941_, v_macroStack_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1950_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_box(0);
v___x_1952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3));
v___x_1953_ = l_Lean_mkConst(v___x_1952_, v___x_1951_);
return v___x_1953_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0);
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(lean_object* v_cfg_1956_, lean_object* v_cfgItem_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1);
v___x_1966_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1956_, v_cfgItem_1957_, v___x_1965_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_1967_, lean_object* v_cfgItem_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(v_cfg_1967_, v_cfgItem_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_cfgItem_1968_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_cfg_1978_, lean_object* v_init_1979_, uint8_t v_logExceptions_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_onErr_1985_; lean_object* v_eval_1986_; 
v_onErr_1985_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v_eval_1986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_1980_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1986_, v_init_1979_, v_cfg_1978_, v_onErr_1985_, v_logExceptions_1980_, v_a_1982_, v_a_1983_);
return v___x_1987_;
}
else
{
uint8_t v_recover_1988_; lean_object* v___x_1989_; 
v_recover_1988_ = lean_ctor_get_uint8(v_a_1981_, sizeof(void*)*1);
v___x_1989_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1986_, v_init_1979_, v_cfg_1978_, v_onErr_1985_, v_recover_1988_, v_a_1982_, v_a_1983_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_cfg_1990_, lean_object* v_init_1991_, lean_object* v_logExceptions_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
uint8_t v_logExceptions_boxed_1997_; lean_object* v_res_1998_; 
v_logExceptions_boxed_1997_ = lean_unbox(v_logExceptions_1992_);
v_res_1998_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_1990_, v_init_1991_, v_logExceptions_boxed_1997_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec_ref(v_a_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_cfg_1999_, lean_object* v_init_2000_, uint8_t v_logExceptions_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_cfg_1999_, v_init_2000_, v_logExceptions_2001_, v_a_2002_, v_a_2008_, v_a_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_cfg_2012_, lean_object* v_init_2013_, lean_object* v_logExceptions_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
uint8_t v_logExceptions_boxed_2024_; lean_object* v_res_2025_; 
v_logExceptions_boxed_2024_ = lean_unbox(v_logExceptions_2014_);
v_res_2025_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_cfg_2012_, v_init_2013_, v_logExceptions_boxed_2024_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_box(0);
v___x_2027_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object* v_msg_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_ref_2062_; lean_object* v___x_2063_; lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v_ref_2062_ = lean_ctor_get(v___y_2059_, 5);
v___x_2063_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_inc(v_ref_2062_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_ref_2062_);
lean_ctor_set(v___x_2068_, 1, v_a_2064_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 1);
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v_msg_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
return v_res_2079_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_2082_ = l_Lean_stringToMessageData(v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_2094_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2093_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_x_2095_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_2106_, lean_object* v___x_2107_, lean_object* v_a_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2110_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_2119_, v_h_2106_, v___x_2107_, v_a_2108_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_fst_2122_; lean_object* v_snd_2123_; lean_object* v_fst_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2149_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_fst_2122_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fst_2122_);
v_snd_2123_ = lean_ctor_get(v_a_2121_, 1);
lean_inc(v_snd_2123_);
lean_dec(v_a_2121_);
v_fst_2124_ = lean_ctor_get(v_fst_2122_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_fst_2122_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_fst_2122_, 1);
lean_dec(v_unused_2150_);
v___x_2126_ = v_fst_2122_;
v_isShared_2127_ = v_isSharedCheck_2149_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_fst_2124_);
lean_dec(v_fst_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2149_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_box(0);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 1);
lean_ctor_set(v___x_2126_, 1, v___x_2128_);
lean_ctor_set(v___x_2126_, 0, v_snd_2123_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_snd_2123_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2130_, v___y_2110_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2139_);
v___x_2133_ = v___x_2131_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v___x_2131_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v_fst_2124_);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2124_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_fst_2124_);
v_a_2140_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2131_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2120_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2120_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v_a_2108_);
lean_dec(v___x_2107_);
lean_dec(v_h_2106_);
v_a_2159_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2118_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2118_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_2167_, lean_object* v___x_2168_, lean_object* v_a_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_2167_, v___x_2168_, v_a_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_2180_, lean_object* v_a_2181_, lean_object* v_ids_2182_, lean_object* v_h_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___f_2193_; lean_object* v___x_2194_; 
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2193_, 0, v_h_2183_);
lean_closure_set(v___f_2193_, 1, v___x_2180_);
lean_closure_set(v___f_2193_, 2, v_a_2181_);
v___x_2194_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2193_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2182_, v_a_2195_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2196_;
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_ids_2182_);
v_a_2197_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2194_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2194_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_2205_, lean_object* v_a_2206_, lean_object* v_ids_2207_, lean_object* v_h_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_2205_, v_a_2206_, v_ids_2207_, v_h_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_2219_, lean_object* v_a_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2222_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l_Lean_MVarId_extractLets(v_a_2231_, v___x_2219_, v_a_2220_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v_fst_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2261_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_fst_2234_ = lean_ctor_get(v_a_2233_, 0);
lean_inc(v_fst_2234_);
v_snd_2235_ = lean_ctor_get(v_a_2233_, 1);
lean_inc(v_snd_2235_);
lean_dec(v_a_2233_);
v_fst_2236_ = lean_ctor_get(v_fst_2234_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_fst_2234_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; 
v_unused_2262_ = lean_ctor_get(v_fst_2234_, 1);
lean_dec(v_unused_2262_);
v___x_2238_ = v_fst_2234_;
v_isShared_2239_ = v_isSharedCheck_2261_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_fst_2236_);
lean_dec(v_fst_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2261_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 1);
lean_ctor_set(v___x_2238_, 1, v___x_2240_);
lean_ctor_set(v___x_2238_, 0, v_snd_2235_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_snd_2235_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2242_, v___y_2222_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2243_, 0);
lean_dec(v_unused_2251_);
v___x_2245_ = v___x_2243_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_dec(v___x_2243_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_fst_2236_);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_fst_2236_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_fst_2236_);
v_a_2252_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2243_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2243_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2263_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2232_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2232_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_a_2220_);
lean_dec(v___x_2219_);
v_a_2271_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2230_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2230_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_2279_, lean_object* v_a_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_2279_, v_a_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_2291_, lean_object* v_ids_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2291_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_2292_, v_a_2303_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2304_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_ids_2292_);
v_a_2305_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2302_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2302_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_2313_, lean_object* v_ids_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_2313_, v_ids_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_2325_, size_t v_i_2326_, lean_object* v_bs_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_usize_dec_lt(v_i_2326_, v_sz_2325_);
if (v___x_2328_ == 0)
{
return v_bs_2327_;
}
else
{
lean_object* v_v_2329_; lean_object* v___x_2330_; lean_object* v_bs_x27_2331_; lean_object* v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v_v_2329_ = lean_array_uget(v_bs_2327_, v_i_2326_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v_bs_x27_2331_ = lean_array_uset(v_bs_2327_, v_i_2326_, v___x_2330_);
v___x_2332_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_2329_);
lean_dec(v_v_2329_);
v___x_2333_ = ((size_t)1ULL);
v___x_2334_ = lean_usize_add(v_i_2326_, v___x_2333_);
v___x_2335_ = lean_array_uset(v_bs_x27_2331_, v_i_2326_, v___x_2332_);
v_i_2326_ = v___x_2334_;
v_bs_2327_ = v___x_2335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_2337_, lean_object* v_i_2338_, lean_object* v_bs_2339_){
_start:
{
size_t v_sz_boxed_2340_; size_t v_i_boxed_2341_; lean_object* v_res_2342_; 
v_sz_boxed_2340_ = lean_unbox_usize(v_sz_2337_);
lean_dec(v_sz_2337_);
v_i_boxed_2341_ = lean_unbox_usize(v_i_2338_);
lean_dec(v_i_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_2340_, v_i_boxed_2341_, v_bs_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_2363_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_x_2363_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_dec(v_x_2363_);
v___x_2391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = l_Lean_Syntax_getArg(v_x_2363_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2393_);
v___x_2395_ = l_Lean_Syntax_isOfKind(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec(v___x_2393_);
lean_dec(v_x_2363_);
v___x_2396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2396_;
}
else
{
lean_object* v___f_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v_loc_x3f_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___f_2397_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = l_Lean_Syntax_getArg(v_x_2363_, v___x_2398_);
v___x_2439_ = lean_unsigned_to_nat(3u);
v___x_2440_ = l_Lean_Syntax_getArg(v_x_2363_, v___x_2439_);
lean_dec(v_x_2363_);
v___x_2441_ = l_Lean_Syntax_isNone(v___x_2440_);
if (v___x_2441_ == 0)
{
uint8_t v___x_2442_; 
lean_inc(v___x_2440_);
v___x_2442_ = l_Lean_Syntax_matchesNull(v___x_2440_, v___x_2392_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec(v___x_2440_);
lean_dec(v___x_2399_);
lean_dec(v___x_2393_);
v___x_2443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2443_;
}
else
{
lean_object* v___x_2444_; lean_object* v_loc_x3f_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2445_ = l_Lean_Syntax_getArg(v___x_2440_, v___x_2444_);
lean_dec(v___x_2440_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2445_);
v___x_2447_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec(v_loc_x3f_2445_);
lean_dec(v___x_2399_);
lean_dec(v___x_2393_);
v___x_2448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_loc_x3f_2445_);
v_loc_x3f_2401_ = v___x_2449_;
v___y_2402_ = v_a_2364_;
v___y_2403_ = v_a_2365_;
v___y_2404_ = v_a_2366_;
v___y_2405_ = v_a_2367_;
v___y_2406_ = v_a_2368_;
v___y_2407_ = v_a_2369_;
v___y_2408_ = v_a_2370_;
v___y_2409_ = v_a_2371_;
goto v___jp_2400_;
}
}
}
else
{
lean_object* v___x_2450_; 
lean_dec(v___x_2440_);
v___x_2450_ = lean_box(0);
v_loc_x3f_2401_ = v___x_2450_;
v___y_2402_ = v_a_2364_;
v___y_2403_ = v_a_2365_;
v___y_2404_ = v_a_2366_;
v___y_2405_ = v_a_2367_;
v___y_2406_ = v_a_2368_;
v___y_2407_ = v_a_2369_;
v___y_2408_ = v_a_2370_;
v___y_2409_ = v_a_2371_;
goto v___jp_2400_;
}
v___jp_2400_:
{
uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = 0;
v___x_2411_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2411_, 0, v___x_2410_);
lean_ctor_set_uint8(v___x_2411_, 1, v___x_2395_);
lean_ctor_set_uint8(v___x_2411_, 2, v___x_2410_);
lean_ctor_set_uint8(v___x_2411_, 3, v___x_2395_);
lean_ctor_set_uint8(v___x_2411_, 4, v___x_2395_);
lean_ctor_set_uint8(v___x_2411_, 5, v___x_2410_);
lean_ctor_set_uint8(v___x_2411_, 6, v___x_2395_);
lean_ctor_set_uint8(v___x_2411_, 7, v___x_2395_);
lean_ctor_set_uint8(v___x_2411_, 8, v___x_2410_);
lean_ctor_set_uint8(v___x_2411_, 9, v___x_2410_);
lean_ctor_set_uint8(v___x_2411_, 10, v___x_2410_);
v___x_2412_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_2393_, v___x_2411_, v___x_2395_, v___y_2402_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v_ids_2414_; size_t v_sz_2415_; size_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___f_2421_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_n(v_a_2413_, 2);
lean_dec_ref_known(v___x_2412_, 1);
v_ids_2414_ = l_Lean_Syntax_getArgs(v___x_2399_);
lean_dec(v___x_2399_);
v_sz_2415_ = lean_array_size(v_ids_2414_);
v___x_2416_ = ((size_t)0ULL);
lean_inc_ref_n(v_ids_2414_, 2);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_2415_, v___x_2416_, v_ids_2414_);
v___x_2418_ = lean_array_to_list(v___x_2417_);
lean_inc(v___x_2418_);
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_2419_, 0, v___x_2418_);
lean_closure_set(v___f_2419_, 1, v_a_2413_);
lean_closure_set(v___f_2419_, 2, v_ids_2414_);
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2420_, 0, v___x_2418_);
lean_closure_set(v___f_2420_, 1, v_a_2413_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_2421_, 0, v___f_2420_);
lean_closure_set(v___f_2421_, 1, v_ids_2414_);
if (lean_obj_tag(v_loc_x3f_2401_) == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_box(0);
v___y_2374_ = v___y_2408_;
v___y_2375_ = v___y_2409_;
v___y_2376_ = v___y_2403_;
v___y_2377_ = v___f_2397_;
v___y_2378_ = v___y_2405_;
v___y_2379_ = v___y_2407_;
v___y_2380_ = v___y_2402_;
v___y_2381_ = v___f_2421_;
v___y_2382_ = v___y_2406_;
v___y_2383_ = v___f_2419_;
v___y_2384_ = v___y_2404_;
v___y_2385_ = v___x_2422_;
goto v___jp_2373_;
}
else
{
lean_object* v_val_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
v_val_2423_ = lean_ctor_get(v_loc_x3f_2401_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_loc_x3f_2401_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v_loc_x3f_2401_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_val_2423_);
lean_dec(v_loc_x3f_2401_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_val_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
v___y_2374_ = v___y_2408_;
v___y_2375_ = v___y_2409_;
v___y_2376_ = v___y_2403_;
v___y_2377_ = v___f_2397_;
v___y_2378_ = v___y_2405_;
v___y_2379_ = v___y_2407_;
v___y_2380_ = v___y_2402_;
v___y_2381_ = v___f_2421_;
v___y_2382_ = v___y_2406_;
v___y_2383_ = v___f_2419_;
v___y_2384_ = v___y_2404_;
v___y_2385_ = v___x_2428_;
goto v___jp_2373_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_loc_x3f_2401_);
lean_dec(v___x_2399_);
v_a_2431_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2412_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2412_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
v___jp_2373_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = l_Lean_mkOptionalNode(v___y_2385_);
v___x_2387_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2386_);
lean_dec(v___x_2386_);
lean_inc_ref(v___y_2377_);
v___x_2388_ = l_Lean_Elab_Tactic_withLocation(v___x_2387_, v___y_2383_, v___y_2381_, v___y_2377_, v___y_2380_, v___y_2376_, v___y_2384_, v___y_2378_, v___y_2382_, v___y_2379_, v___y_2374_, v___y_2375_);
lean_dec(v___x_2387_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_2462_, lean_object* v_msg_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_2463_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_2474_, lean_object* v_msg_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_2474_, v_msg_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2493_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2494_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_2496_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_2497_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(lean_object* v_ctor_2500_, lean_object* v_args_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0));
v___x_2529_ = lean_string_dec_eq(v_ctor_2500_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2531_ = lean_array_get_size(v_args_2501_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_dec_eq(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
v___x_2535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_2534_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
goto v___jp_2507_;
}
}
v___jp_2507_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2508_ = l_Lean_instInhabitedExpr;
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = lean_array_get_borrowed(v___x_2508_, v_args_2501_, v___x_2509_);
lean_inc(v___x_2510_);
v___x_2511_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v___x_2510_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2511_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2511_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_2544_, lean_object* v_args_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(v_ctor_2544_, v_args_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_args_2545_);
lean_dec_ref(v_ctor_2544_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___f_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___f_2564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0));
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2566_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2565_, v___f_2564_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
return v_res_2573_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_box(0);
v___x_2576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2577_ = l_Lean_Expr_const___override(v___x_2576_, v___x_2575_);
return v___x_2577_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0));
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig(void){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
v___x_2585_ = l_Lean_MessageData_ofExpr(v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0);
v___x_2587_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2586_);
return v___x_2588_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
v___x_2590_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(lean_object* v_stx_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_ty_x3f_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_fileName_2606_; lean_object* v_fileMap_2607_; lean_object* v_options_2608_; lean_object* v_currRecDepth_2609_; lean_object* v_maxRecDepth_2610_; lean_object* v_ref_2611_; lean_object* v_currNamespace_2612_; lean_object* v_openDecls_2613_; lean_object* v_initHeartbeats_2614_; lean_object* v_maxHeartbeats_2615_; lean_object* v_quotContext_2616_; lean_object* v_currMacroScope_2617_; uint8_t v_diag_2618_; lean_object* v_cancelTk_x3f_2619_; uint8_t v_suppressElabErrors_2620_; lean_object* v_inheritedTraceOptions_2621_; uint8_t v___x_2622_; lean_object* v_ref_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_ty_x3f_2600_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2, &l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
v___x_2601_ = 1;
v___x_2602_ = lean_box(0);
v___x_2603_ = lean_box(v___x_2601_);
v___x_2604_ = lean_box(v___x_2601_);
lean_inc(v_stx_2592_);
v___x_2605_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2605_, 0, v_stx_2592_);
lean_closure_set(v___x_2605_, 1, v_ty_x3f_2600_);
lean_closure_set(v___x_2605_, 2, v___x_2603_);
lean_closure_set(v___x_2605_, 3, v___x_2604_);
lean_closure_set(v___x_2605_, 4, v___x_2602_);
v_fileName_2606_ = lean_ctor_get(v_a_2597_, 0);
v_fileMap_2607_ = lean_ctor_get(v_a_2597_, 1);
v_options_2608_ = lean_ctor_get(v_a_2597_, 2);
v_currRecDepth_2609_ = lean_ctor_get(v_a_2597_, 3);
v_maxRecDepth_2610_ = lean_ctor_get(v_a_2597_, 4);
v_ref_2611_ = lean_ctor_get(v_a_2597_, 5);
v_currNamespace_2612_ = lean_ctor_get(v_a_2597_, 6);
v_openDecls_2613_ = lean_ctor_get(v_a_2597_, 7);
v_initHeartbeats_2614_ = lean_ctor_get(v_a_2597_, 8);
v_maxHeartbeats_2615_ = lean_ctor_get(v_a_2597_, 9);
v_quotContext_2616_ = lean_ctor_get(v_a_2597_, 10);
v_currMacroScope_2617_ = lean_ctor_get(v_a_2597_, 11);
v_diag_2618_ = lean_ctor_get_uint8(v_a_2597_, sizeof(void*)*14);
v_cancelTk_x3f_2619_ = lean_ctor_get(v_a_2597_, 12);
v_suppressElabErrors_2620_ = lean_ctor_get_uint8(v_a_2597_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2621_ = lean_ctor_get(v_a_2597_, 13);
v___x_2622_ = 1;
v_ref_2623_ = l_Lean_replaceRef(v_stx_2592_, v_ref_2611_);
lean_dec(v_stx_2592_);
lean_inc_ref(v_inheritedTraceOptions_2621_);
lean_inc(v_cancelTk_x3f_2619_);
lean_inc(v_currMacroScope_2617_);
lean_inc(v_quotContext_2616_);
lean_inc(v_maxHeartbeats_2615_);
lean_inc(v_initHeartbeats_2614_);
lean_inc(v_openDecls_2613_);
lean_inc(v_currNamespace_2612_);
lean_inc(v_maxRecDepth_2610_);
lean_inc(v_currRecDepth_2609_);
lean_inc_ref(v_options_2608_);
lean_inc_ref(v_fileMap_2607_);
lean_inc_ref(v_fileName_2606_);
v___x_2624_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2624_, 0, v_fileName_2606_);
lean_ctor_set(v___x_2624_, 1, v_fileMap_2607_);
lean_ctor_set(v___x_2624_, 2, v_options_2608_);
lean_ctor_set(v___x_2624_, 3, v_currRecDepth_2609_);
lean_ctor_set(v___x_2624_, 4, v_maxRecDepth_2610_);
lean_ctor_set(v___x_2624_, 5, v_ref_2623_);
lean_ctor_set(v___x_2624_, 6, v_currNamespace_2612_);
lean_ctor_set(v___x_2624_, 7, v_openDecls_2613_);
lean_ctor_set(v___x_2624_, 8, v_initHeartbeats_2614_);
lean_ctor_set(v___x_2624_, 9, v_maxHeartbeats_2615_);
lean_ctor_set(v___x_2624_, 10, v_quotContext_2616_);
lean_ctor_set(v___x_2624_, 11, v_currMacroScope_2617_);
lean_ctor_set(v___x_2624_, 12, v_cancelTk_x3f_2619_);
lean_ctor_set(v___x_2624_, 13, v_inheritedTraceOptions_2621_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*14, v_diag_2618_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*14 + 1, v_suppressElabErrors_2620_);
v___x_2625_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2605_, v___x_2622_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v___x_2624_, v_a_2598_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v_a_2628_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; uint8_t v___x_2723_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_2626_, v_a_2596_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2723_ = l_Lean_Expr_hasSorry(v_a_2628_);
if (v___x_2723_ == 0)
{
v___y_2668_ = v_a_2593_;
v___y_2669_ = v_a_2594_;
v___y_2670_ = v_a_2595_;
v___y_2671_ = v_a_2596_;
v___y_2672_ = v___x_2624_;
v___y_2673_ = v_a_2598_;
goto v___jp_2667_;
}
else
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_Expr_hasSyntheticSorry(v_a_2628_);
if (v___x_2724_ == 0)
{
v___y_2705_ = v_a_2593_;
v___y_2706_ = v_a_2594_;
v___y_2707_ = v_a_2595_;
v___y_2708_ = v_a_2596_;
v___y_2709_ = v___x_2624_;
v___y_2710_ = v_a_2598_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2725_; lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2628_);
lean_dec_ref_known(v___x_2624_, 14);
v___x_2725_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
v___jp_2629_:
{
if (v___y_2639_ == 0)
{
if (lean_obj_tag(v___y_2632_) == 0)
{
lean_dec_ref_known(v___y_2632_, 2);
lean_dec_ref(v___y_2635_);
lean_dec(v_a_2628_);
return v___y_2631_;
}
else
{
lean_object* v_id_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2653_; 
v_id_2640_ = lean_ctor_get(v___y_2632_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___y_2632_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___y_2632_, 1);
lean_dec(v_unused_2654_);
v___x_2642_ = v___y_2632_;
v_isShared_2643_ = v_isSharedCheck_2653_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_id_2640_);
lean_dec(v___y_2632_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2653_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; 
v___x_2644_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2637_, v_id_2640_);
lean_dec(v_id_2640_);
if (v___x_2644_ == 0)
{
lean_del_object(v___x_2642_);
lean_dec_ref(v___y_2635_);
lean_dec(v_a_2628_);
return v___y_2631_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec_ref(v___y_2631_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2);
v___x_2646_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
v___x_2647_ = l_Lean_indentExpr(v_a_2628_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 7);
lean_ctor_set(v___x_2642_, 1, v___x_2647_);
lean_ctor_set(v___x_2642_, 0, v___x_2646_);
v___x_2649_ = v___x_2642_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___x_2645_);
v___x_2651_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2650_, v___y_2638_, v___y_2633_, v___y_2630_, v___y_2636_, v___y_2635_, v___y_2634_);
lean_dec_ref(v___y_2635_);
return v___x_2651_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2632_);
lean_dec(v_a_2628_);
return v___y_2631_;
}
}
v___jp_2655_:
{
lean_object* v___x_2662_; 
lean_inc(v_a_2628_);
v___x_2662_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_2628_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec_ref(v___y_2660_);
lean_dec(v_a_2628_);
return v___x_2662_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
v___x_2664_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2665_ = l_Lean_Exception_isInterrupt(v_a_2663_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
lean_inc(v_a_2663_);
v___x_2666_ = l_Lean_Exception_isRuntime(v_a_2663_);
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___x_2662_;
v___y_2632_ = v_a_2663_;
v___y_2633_ = v___y_2657_;
v___y_2634_ = v___y_2661_;
v___y_2635_ = v___y_2660_;
v___y_2636_ = v___y_2659_;
v___y_2637_ = v___x_2664_;
v___y_2638_ = v___y_2656_;
v___y_2639_ = v___x_2666_;
goto v___jp_2629_;
}
else
{
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___x_2662_;
v___y_2632_ = v_a_2663_;
v___y_2633_ = v___y_2657_;
v___y_2634_ = v___y_2661_;
v___y_2635_ = v___y_2660_;
v___y_2636_ = v___y_2659_;
v___y_2637_ = v___x_2664_;
v___y_2638_ = v___y_2656_;
v___y_2639_ = v___x_2665_;
goto v___jp_2629_;
}
}
}
v___jp_2667_:
{
lean_object* v___x_2674_; 
lean_inc(v_a_2628_);
v___x_2674_ = l_Lean_Meta_getMVars(v_a_2628_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2675_, v___x_2602_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v_a_2675_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; uint8_t v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = lean_unbox(v_a_2677_);
lean_dec(v_a_2677_);
if (v___x_2678_ == 0)
{
v___y_2656_ = v___y_2668_;
v___y_2657_ = v___y_2669_;
v___y_2658_ = v___y_2670_;
v___y_2659_ = v___y_2671_;
v___y_2660_ = v___y_2672_;
v___y_2661_ = v___y_2673_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2679_; lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v___y_2672_);
lean_dec(v_a_2628_);
v___x_2679_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v___y_2672_);
lean_dec(v_a_2628_);
v_a_2688_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2676_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2676_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___y_2672_);
lean_dec(v_a_2628_);
v_a_2696_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2674_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2674_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
v___jp_2704_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v___x_2711_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
v___x_2712_ = l_Lean_indentExpr(v_a_2628_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_2713_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec_ref(v___y_2709_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref_known(v___x_2624_, 14);
v_a_2734_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2625_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2625_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_stx_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(lean_object* v_config_2753_, lean_object* v_item_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_item_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_2773_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2754_, v___x_2772_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2773_) == 0)
{
uint8_t v___x_2774_; 
lean_dec_ref_known(v___x_2773_, 1);
v___x_2774_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_2754_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2775_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_2754_);
lean_inc_ref(v_item_2754_);
v___x_2776_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_2754_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1));
v___x_2778_ = lean_string_dec_lt(v___x_2775_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2));
v___x_2780_ = lean_string_dec_lt(v___x_2775_, v___x_2779_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_string_dec_eq(v___x_2775_, v___x_2779_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3));
v___x_2783_ = lean_string_dec_eq(v___x_2775_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4));
v___x_2785_ = lean_string_dec_eq(v___x_2775_, v___x_2784_);
lean_dec_ref(v___x_2775_);
if (v___x_2785_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5));
v___x_2787_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_2786_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2787_) == 0)
{
uint8_t v___x_2788_; 
lean_dec_ref_known(v___x_2787_, 1);
v___x_2788_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_2788_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2789_; 
lean_dec_ref(v___x_2776_);
v___x_2789_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2815_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2815_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2815_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
uint8_t v_proofs_2794_; uint8_t v_types_2795_; uint8_t v_implicits_2796_; uint8_t v_descend_2797_; uint8_t v_underBinder_2798_; uint8_t v_merge_2799_; uint8_t v_useContext_2800_; uint8_t v_onlyGivenNames_2801_; uint8_t v_preserveBinderNames_2802_; uint8_t v_lift_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2814_; 
v_proofs_2794_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_2795_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_2796_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_2797_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_2798_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_merge_2799_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_2800_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_2801_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_2802_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_2803_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2805_ = v_config_2753_;
v_isShared_2806_ = v_isSharedCheck_2814_;
goto v_resetjp_2804_;
}
else
{
lean_dec(v_config_2753_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2814_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, 0, v_proofs_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, 1, v_types_2795_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, 2, v_implicits_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, 3, v_descend_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, 4, v_underBinder_2798_);
v___x_2808_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
uint8_t v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
lean_ctor_set_uint8(v___x_2808_, 5, v___x_2809_);
lean_ctor_set_uint8(v___x_2808_, 6, v_merge_2799_);
lean_ctor_set_uint8(v___x_2808_, 7, v_useContext_2800_);
lean_ctor_set_uint8(v___x_2808_, 8, v_onlyGivenNames_2801_);
lean_ctor_set_uint8(v___x_2808_, 9, v_preserveBinderNames_2802_);
lean_ctor_set_uint8(v___x_2808_, 10, v_lift_2803_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2808_);
v___x_2811_ = v___x_2792_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2808_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v_config_2753_);
v_a_2816_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2789_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2789_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
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
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_2824_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2787_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2787_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v___x_2775_);
v___x_2832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6));
v___x_2833_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_2832_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2833_) == 0)
{
uint8_t v___x_2834_; 
lean_dec_ref_known(v___x_2833_, 1);
v___x_2834_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_2834_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2835_; 
lean_dec_ref(v___x_2776_);
v___x_2835_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2861_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2861_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2861_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v_proofs_2840_; uint8_t v_types_2841_; uint8_t v_implicits_2842_; uint8_t v_descend_2843_; uint8_t v_underBinder_2844_; uint8_t v_usedOnly_2845_; uint8_t v_merge_2846_; uint8_t v_onlyGivenNames_2847_; uint8_t v_preserveBinderNames_2848_; uint8_t v_lift_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2860_; 
v_proofs_2840_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_2841_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_2842_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_2843_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_2844_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_2845_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_2846_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_onlyGivenNames_2847_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_2848_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_2849_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2851_ = v_config_2753_;
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v_config_2753_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 0, v_proofs_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 1, v_types_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 2, v_implicits_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 3, v_descend_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 4, v_underBinder_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 5, v_usedOnly_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, 6, v_merge_2846_);
v___x_2854_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
uint8_t v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_unbox(v_a_2836_);
lean_dec(v_a_2836_);
lean_ctor_set_uint8(v___x_2854_, 7, v___x_2855_);
lean_ctor_set_uint8(v___x_2854_, 8, v_onlyGivenNames_2847_);
lean_ctor_set_uint8(v___x_2854_, 9, v_preserveBinderNames_2848_);
lean_ctor_set_uint8(v___x_2854_, 10, v_lift_2849_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2854_);
v___x_2857_ = v___x_2838_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2854_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_config_2753_);
v_a_2862_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2835_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2835_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
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
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_2870_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2833_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2833_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec_ref(v___x_2775_);
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7));
v___x_2879_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_2878_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2879_) == 0)
{
uint8_t v___x_2880_; 
lean_dec_ref_known(v___x_2879_, 1);
v___x_2880_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_2880_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2881_; 
lean_dec_ref(v___x_2776_);
v___x_2881_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2907_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2907_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2907_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
uint8_t v_proofs_2886_; uint8_t v_types_2887_; uint8_t v_implicits_2888_; uint8_t v_descend_2889_; uint8_t v_usedOnly_2890_; uint8_t v_merge_2891_; uint8_t v_useContext_2892_; uint8_t v_onlyGivenNames_2893_; uint8_t v_preserveBinderNames_2894_; uint8_t v_lift_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2906_; 
v_proofs_2886_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_2887_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_2888_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_2889_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_usedOnly_2890_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_2891_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_2892_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_2893_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_2894_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_2895_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2897_ = v_config_2753_;
v_isShared_2898_ = v_isSharedCheck_2906_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v_config_2753_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2906_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, 0, v_proofs_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, 1, v_types_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, 2, v_implicits_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, 3, v_descend_2889_);
v___x_2900_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
uint8_t v___x_2901_; lean_object* v___x_2903_; 
v___x_2901_ = lean_unbox(v_a_2882_);
lean_dec(v_a_2882_);
lean_ctor_set_uint8(v___x_2900_, 4, v___x_2901_);
lean_ctor_set_uint8(v___x_2900_, 5, v_usedOnly_2890_);
lean_ctor_set_uint8(v___x_2900_, 6, v_merge_2891_);
lean_ctor_set_uint8(v___x_2900_, 7, v_useContext_2892_);
lean_ctor_set_uint8(v___x_2900_, 8, v_onlyGivenNames_2893_);
lean_ctor_set_uint8(v___x_2900_, 9, v_preserveBinderNames_2894_);
lean_ctor_set_uint8(v___x_2900_, 10, v_lift_2895_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2900_);
v___x_2903_ = v___x_2884_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2900_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_config_2753_);
v_a_2908_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2881_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2881_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
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
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_2916_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2879_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2879_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
else
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_string_dec_eq(v___x_2775_, v___x_2777_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8));
v___x_2926_ = lean_string_dec_eq(v___x_2775_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9));
v___x_2928_ = lean_string_dec_eq(v___x_2775_, v___x_2927_);
lean_dec_ref(v___x_2775_);
if (v___x_2928_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10));
v___x_2930_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_2929_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2930_) == 0)
{
uint8_t v___x_2931_; 
lean_dec_ref_known(v___x_2930_, 1);
v___x_2931_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_2931_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2932_; 
lean_dec_ref(v___x_2776_);
v___x_2932_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2958_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2958_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2958_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
uint8_t v_proofs_2937_; uint8_t v_implicits_2938_; uint8_t v_descend_2939_; uint8_t v_underBinder_2940_; uint8_t v_usedOnly_2941_; uint8_t v_merge_2942_; uint8_t v_useContext_2943_; uint8_t v_onlyGivenNames_2944_; uint8_t v_preserveBinderNames_2945_; uint8_t v_lift_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2957_; 
v_proofs_2937_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_implicits_2938_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_2939_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_2940_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_2941_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_2942_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_2943_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_2944_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_2945_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_2946_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2948_ = v_config_2753_;
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
else
{
lean_dec(v_config_2753_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_2956_, 0, v_proofs_2937_);
v___x_2951_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
uint8_t v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_unbox(v_a_2933_);
lean_dec(v_a_2933_);
lean_ctor_set_uint8(v___x_2951_, 1, v___x_2952_);
lean_ctor_set_uint8(v___x_2951_, 2, v_implicits_2938_);
lean_ctor_set_uint8(v___x_2951_, 3, v_descend_2939_);
lean_ctor_set_uint8(v___x_2951_, 4, v_underBinder_2940_);
lean_ctor_set_uint8(v___x_2951_, 5, v_usedOnly_2941_);
lean_ctor_set_uint8(v___x_2951_, 6, v_merge_2942_);
lean_ctor_set_uint8(v___x_2951_, 7, v_useContext_2943_);
lean_ctor_set_uint8(v___x_2951_, 8, v_onlyGivenNames_2944_);
lean_ctor_set_uint8(v___x_2951_, 9, v_preserveBinderNames_2945_);
lean_ctor_set_uint8(v___x_2951_, 10, v_lift_2946_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2951_);
v___x_2954_ = v___x_2935_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2951_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v_config_2753_);
v_a_2959_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2932_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2932_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
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
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_2967_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2930_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2930_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec_ref(v___x_2775_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11));
v___x_2976_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_2975_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2976_) == 0)
{
uint8_t v___x_2977_; 
lean_dec_ref_known(v___x_2976_, 1);
v___x_2977_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_2977_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2978_; 
lean_dec_ref(v___x_2776_);
v___x_2978_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3004_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_3004_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3004_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
uint8_t v_types_2983_; uint8_t v_implicits_2984_; uint8_t v_descend_2985_; uint8_t v_underBinder_2986_; uint8_t v_usedOnly_2987_; uint8_t v_merge_2988_; uint8_t v_useContext_2989_; uint8_t v_onlyGivenNames_2990_; uint8_t v_preserveBinderNames_2991_; uint8_t v_lift_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3003_; 
v_types_2983_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_2984_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_2985_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_2986_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_2987_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_2988_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_2989_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_2990_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_2991_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_2992_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2994_ = v_config_2753_;
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
else
{
lean_dec(v_config_2753_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 0, 11);
v___x_2997_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
uint8_t v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = lean_unbox(v_a_2979_);
lean_dec(v_a_2979_);
lean_ctor_set_uint8(v___x_2997_, 0, v___x_2998_);
lean_ctor_set_uint8(v___x_2997_, 1, v_types_2983_);
lean_ctor_set_uint8(v___x_2997_, 2, v_implicits_2984_);
lean_ctor_set_uint8(v___x_2997_, 3, v_descend_2985_);
lean_ctor_set_uint8(v___x_2997_, 4, v_underBinder_2986_);
lean_ctor_set_uint8(v___x_2997_, 5, v_usedOnly_2987_);
lean_ctor_set_uint8(v___x_2997_, 6, v_merge_2988_);
lean_ctor_set_uint8(v___x_2997_, 7, v_useContext_2989_);
lean_ctor_set_uint8(v___x_2997_, 8, v_onlyGivenNames_2990_);
lean_ctor_set_uint8(v___x_2997_, 9, v_preserveBinderNames_2991_);
lean_ctor_set_uint8(v___x_2997_, 10, v_lift_2992_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2997_);
v___x_3000_ = v___x_2981_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2997_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_config_2753_);
v_a_3005_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2978_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2978_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
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
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3013_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2976_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2976_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v___x_2775_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12));
v___x_3022_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3021_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3022_) == 0)
{
uint8_t v___x_3023_; 
lean_dec_ref_known(v___x_3022_, 1);
v___x_3023_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3023_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3024_; 
lean_dec_ref(v___x_2776_);
v___x_3024_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3050_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
uint8_t v_proofs_3029_; uint8_t v_types_3030_; uint8_t v_implicits_3031_; uint8_t v_descend_3032_; uint8_t v_underBinder_3033_; uint8_t v_usedOnly_3034_; uint8_t v_merge_3035_; uint8_t v_useContext_3036_; uint8_t v_onlyGivenNames_3037_; uint8_t v_lift_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3049_; 
v_proofs_3029_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3030_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_3031_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_3032_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_3033_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3034_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_3035_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_3036_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_3037_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_lift_3038_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3040_ = v_config_2753_;
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v_config_2753_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 0, v_proofs_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 1, v_types_3030_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 2, v_implicits_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 3, v_descend_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 4, v_underBinder_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 5, v_usedOnly_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 6, v_merge_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 7, v_useContext_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, 8, v_onlyGivenNames_3037_);
v___x_3043_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
uint8_t v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = lean_unbox(v_a_3025_);
lean_dec(v_a_3025_);
lean_ctor_set_uint8(v___x_3043_, 9, v___x_3044_);
lean_ctor_set_uint8(v___x_3043_, 10, v_lift_3038_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3043_);
v___x_3046_ = v___x_3027_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3043_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_config_2753_);
v_a_3051_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3024_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3024_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
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
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3059_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3022_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3022_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
else
{
lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13));
v___x_3068_ = lean_string_dec_lt(v___x_2775_, v___x_3067_);
if (v___x_3068_ == 0)
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_string_dec_eq(v___x_2775_, v___x_3067_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14));
v___x_3071_ = lean_string_dec_eq(v___x_2775_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15));
v___x_3073_ = lean_string_dec_eq(v___x_2775_, v___x_3072_);
lean_dec_ref(v___x_2775_);
if (v___x_3073_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16));
v___x_3075_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3074_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3075_) == 0)
{
uint8_t v___x_3076_; 
lean_dec_ref_known(v___x_3075_, 1);
v___x_3076_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3076_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3077_; 
lean_dec_ref(v___x_2776_);
v___x_3077_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3103_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3103_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3103_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v_proofs_3082_; uint8_t v_types_3083_; uint8_t v_implicits_3084_; uint8_t v_descend_3085_; uint8_t v_underBinder_3086_; uint8_t v_usedOnly_3087_; uint8_t v_merge_3088_; uint8_t v_useContext_3089_; uint8_t v_preserveBinderNames_3090_; uint8_t v_lift_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3102_; 
v_proofs_3082_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3083_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_3084_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_3085_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_3086_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3087_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_3088_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_3089_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_preserveBinderNames_3090_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_3091_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3093_ = v_config_2753_;
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v_config_2753_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 0, v_proofs_3082_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 1, v_types_3083_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 2, v_implicits_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 3, v_descend_3085_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 4, v_underBinder_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 5, v_usedOnly_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 6, v_merge_3088_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, 7, v_useContext_3089_);
v___x_3096_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
uint8_t v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_unbox(v_a_3078_);
lean_dec(v_a_3078_);
lean_ctor_set_uint8(v___x_3096_, 8, v___x_3097_);
lean_ctor_set_uint8(v___x_3096_, 9, v_preserveBinderNames_3090_);
lean_ctor_set_uint8(v___x_3096_, 10, v_lift_3091_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3096_);
v___x_3099_ = v___x_3080_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3096_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v_config_2753_);
v_a_3104_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3077_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3077_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
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
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3112_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3075_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3075_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_dec_ref(v___x_2775_);
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17));
v___x_3121_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3120_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3121_) == 0)
{
uint8_t v___x_3122_; 
lean_dec_ref_known(v___x_3121_, 1);
v___x_3122_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3122_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3123_; 
lean_dec_ref(v___x_2776_);
v___x_3123_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3149_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3149_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3149_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
uint8_t v_proofs_3128_; uint8_t v_types_3129_; uint8_t v_implicits_3130_; uint8_t v_descend_3131_; uint8_t v_underBinder_3132_; uint8_t v_usedOnly_3133_; uint8_t v_useContext_3134_; uint8_t v_onlyGivenNames_3135_; uint8_t v_preserveBinderNames_3136_; uint8_t v_lift_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3148_; 
v_proofs_3128_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3129_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_3130_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_3131_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_3132_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3133_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_useContext_3134_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_3135_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_3136_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_3137_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3139_ = v_config_2753_;
v_isShared_3140_ = v_isSharedCheck_3148_;
goto v_resetjp_3138_;
}
else
{
lean_dec(v_config_2753_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3148_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 0, v_proofs_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 1, v_types_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 2, v_implicits_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 3, v_descend_3131_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 4, v_underBinder_3132_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, 5, v_usedOnly_3133_);
v___x_3142_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
uint8_t v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = lean_unbox(v_a_3124_);
lean_dec(v_a_3124_);
lean_ctor_set_uint8(v___x_3142_, 6, v___x_3143_);
lean_ctor_set_uint8(v___x_3142_, 7, v_useContext_3134_);
lean_ctor_set_uint8(v___x_3142_, 8, v_onlyGivenNames_3135_);
lean_ctor_set_uint8(v___x_3142_, 9, v_preserveBinderNames_3136_);
lean_ctor_set_uint8(v___x_3142_, 10, v_lift_3137_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3142_);
v___x_3145_ = v___x_3126_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3142_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_config_2753_);
v_a_3150_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3123_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3123_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
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
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3158_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3121_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3121_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec_ref(v___x_2775_);
v___x_3166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18));
v___x_3167_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3166_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3167_) == 0)
{
uint8_t v___x_3168_; 
lean_dec_ref_known(v___x_3167_, 1);
v___x_3168_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3169_; 
lean_dec_ref(v___x_2776_);
v___x_3169_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3195_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3195_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3195_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v_proofs_3174_; uint8_t v_types_3175_; uint8_t v_implicits_3176_; uint8_t v_descend_3177_; uint8_t v_underBinder_3178_; uint8_t v_usedOnly_3179_; uint8_t v_merge_3180_; uint8_t v_useContext_3181_; uint8_t v_onlyGivenNames_3182_; uint8_t v_preserveBinderNames_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3194_; 
v_proofs_3174_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3175_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_3176_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_descend_3177_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_3178_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3179_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_3180_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_3181_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_3182_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_3183_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3185_ = v_config_2753_;
v_isShared_3186_ = v_isSharedCheck_3194_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v_config_2753_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3194_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 0, v_proofs_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 1, v_types_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 2, v_implicits_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 3, v_descend_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 4, v_underBinder_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 5, v_usedOnly_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 6, v_merge_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 7, v_useContext_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 8, v_onlyGivenNames_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, 9, v_preserveBinderNames_3183_);
v___x_3188_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
uint8_t v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unbox(v_a_3170_);
lean_dec(v_a_3170_);
lean_ctor_set_uint8(v___x_3188_, 10, v___x_3189_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3188_);
v___x_3191_ = v___x_3172_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3188_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_config_2753_);
v_a_3196_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3169_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3169_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
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
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3204_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3167_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3167_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
else
{
lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19));
v___x_3213_ = lean_string_dec_eq(v___x_2775_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20));
v___x_3215_ = lean_string_dec_eq(v___x_2775_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21));
v___x_3217_ = lean_string_dec_eq(v___x_2775_, v___x_3216_);
lean_dec_ref(v___x_2775_);
if (v___x_3217_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22));
v___x_3219_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3218_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3219_) == 0)
{
uint8_t v___x_3220_; 
lean_dec_ref_known(v___x_3219_, 1);
v___x_3220_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3220_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3221_; 
lean_dec_ref(v___x_2776_);
v___x_3221_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3247_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3247_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3247_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
uint8_t v_proofs_3226_; uint8_t v_types_3227_; uint8_t v_descend_3228_; uint8_t v_underBinder_3229_; uint8_t v_usedOnly_3230_; uint8_t v_merge_3231_; uint8_t v_useContext_3232_; uint8_t v_onlyGivenNames_3233_; uint8_t v_preserveBinderNames_3234_; uint8_t v_lift_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3246_; 
v_proofs_3226_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3227_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_descend_3228_ = lean_ctor_get_uint8(v_config_2753_, 3);
v_underBinder_3229_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3230_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_3231_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_3232_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_3233_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_3234_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_3235_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3237_ = v_config_2753_;
v_isShared_3238_ = v_isSharedCheck_3246_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v_config_2753_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3246_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3245_, 0, v_proofs_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3245_, 1, v_types_3227_);
v___x_3240_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
uint8_t v___x_3241_; lean_object* v___x_3243_; 
v___x_3241_ = lean_unbox(v_a_3222_);
lean_dec(v_a_3222_);
lean_ctor_set_uint8(v___x_3240_, 2, v___x_3241_);
lean_ctor_set_uint8(v___x_3240_, 3, v_descend_3228_);
lean_ctor_set_uint8(v___x_3240_, 4, v_underBinder_3229_);
lean_ctor_set_uint8(v___x_3240_, 5, v_usedOnly_3230_);
lean_ctor_set_uint8(v___x_3240_, 6, v_merge_3231_);
lean_ctor_set_uint8(v___x_3240_, 7, v_useContext_3232_);
lean_ctor_set_uint8(v___x_3240_, 8, v_onlyGivenNames_3233_);
lean_ctor_set_uint8(v___x_3240_, 9, v_preserveBinderNames_3234_);
lean_ctor_set_uint8(v___x_3240_, 10, v_lift_3235_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3240_);
v___x_3243_ = v___x_3224_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3240_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_config_2753_);
v_a_3248_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3221_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3221_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
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
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3256_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3219_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3219_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec_ref(v___x_2775_);
v___x_3264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23));
v___x_3265_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_2754_, v___x_3264_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3265_) == 0)
{
uint8_t v___x_3266_; 
lean_dec_ref_known(v___x_3265_, 1);
v___x_3266_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3266_ == 0)
{
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_3267_; 
lean_dec_ref(v___x_2776_);
v___x_3267_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3293_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3270_ = v___x_3267_;
v_isShared_3271_ = v_isSharedCheck_3293_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3293_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
uint8_t v_proofs_3272_; uint8_t v_types_3273_; uint8_t v_implicits_3274_; uint8_t v_underBinder_3275_; uint8_t v_usedOnly_3276_; uint8_t v_merge_3277_; uint8_t v_useContext_3278_; uint8_t v_onlyGivenNames_3279_; uint8_t v_preserveBinderNames_3280_; uint8_t v_lift_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3292_; 
v_proofs_3272_ = lean_ctor_get_uint8(v_config_2753_, 0);
v_types_3273_ = lean_ctor_get_uint8(v_config_2753_, 1);
v_implicits_3274_ = lean_ctor_get_uint8(v_config_2753_, 2);
v_underBinder_3275_ = lean_ctor_get_uint8(v_config_2753_, 4);
v_usedOnly_3276_ = lean_ctor_get_uint8(v_config_2753_, 5);
v_merge_3277_ = lean_ctor_get_uint8(v_config_2753_, 6);
v_useContext_3278_ = lean_ctor_get_uint8(v_config_2753_, 7);
v_onlyGivenNames_3279_ = lean_ctor_get_uint8(v_config_2753_, 8);
v_preserveBinderNames_3280_ = lean_ctor_get_uint8(v_config_2753_, 9);
v_lift_3281_ = lean_ctor_get_uint8(v_config_2753_, 10);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_config_2753_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3283_ = v_config_2753_;
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
else
{
lean_dec(v_config_2753_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3291_, 0, v_proofs_3272_);
lean_ctor_set_uint8(v_reuseFailAlloc_3291_, 1, v_types_3273_);
lean_ctor_set_uint8(v_reuseFailAlloc_3291_, 2, v_implicits_3274_);
v___x_3286_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
uint8_t v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = lean_unbox(v_a_3268_);
lean_dec(v_a_3268_);
lean_ctor_set_uint8(v___x_3286_, 3, v___x_3287_);
lean_ctor_set_uint8(v___x_3286_, 4, v_underBinder_3275_);
lean_ctor_set_uint8(v___x_3286_, 5, v_usedOnly_3276_);
lean_ctor_set_uint8(v___x_3286_, 6, v_merge_3277_);
lean_ctor_set_uint8(v___x_3286_, 7, v_useContext_3278_);
lean_ctor_set_uint8(v___x_3286_, 8, v_onlyGivenNames_3279_);
lean_ctor_set_uint8(v___x_3286_, 9, v_preserveBinderNames_3280_);
lean_ctor_set_uint8(v___x_3286_, 10, v_lift_3281_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3286_);
v___x_3289_ = v___x_3270_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3286_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v_config_2753_);
v_a_3294_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3267_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3267_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
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
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3302_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3265_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3265_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
else
{
uint8_t v___x_3310_; 
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_config_2753_);
v___x_3310_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_2776_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v_item_2754_);
v_item_2763_ = v___x_2776_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v_value_3311_; lean_object* v___x_3312_; 
lean_dec_ref(v___x_2776_);
v_value_3311_ = lean_ctor_get(v_item_2754_, 2);
lean_inc(v_value_3311_);
lean_dec_ref(v_item_2754_);
v___x_3312_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_value_3311_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_3312_;
}
}
}
}
}
else
{
lean_dec_ref(v_config_2753_);
v_item_2763_ = v_item_2754_;
v___y_2764_ = v___y_2755_;
v___y_2765_ = v___y_2756_;
v___y_2766_ = v___y_2757_;
v___y_2767_ = v___y_2758_;
v___y_2768_ = v___y_2759_;
v___y_2769_ = v___y_2760_;
goto v___jp_2762_;
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v_item_2754_);
lean_dec_ref(v_config_2753_);
v_a_3313_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_2773_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_2773_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
v___jp_2762_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0));
v___x_2771_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_2763_, v___x_2770_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3321_, lean_object* v_item_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(v_config_3321_, v_item_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2));
v___x_3335_ = l_Lean_mkConst(v___x_3334_, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(lean_object* v_cfg_3338_, lean_object* v_cfgItem_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1);
v___x_3348_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3338_, v_cfgItem_3339_, v___x_3347_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(lean_object* v_cfg_3349_, lean_object* v_cfgItem_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(v_cfg_3349_, v_cfgItem_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v_cfgItem_3350_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_cfg_3360_, lean_object* v_init_3361_, uint8_t v_logExceptions_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_onErr_3367_; lean_object* v_eval_3368_; 
v_onErr_3367_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0));
v_eval_3368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0));
if (v_logExceptions_3362_ == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3368_, v_init_3361_, v_cfg_3360_, v_onErr_3367_, v_logExceptions_3362_, v_a_3364_, v_a_3365_);
return v___x_3369_;
}
else
{
uint8_t v_recover_3370_; lean_object* v___x_3371_; 
v_recover_3370_ = lean_ctor_get_uint8(v_a_3363_, sizeof(void*)*1);
v___x_3371_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3368_, v_init_3361_, v_cfg_3360_, v_onErr_3367_, v_recover_3370_, v_a_3364_, v_a_3365_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_cfg_3372_, lean_object* v_init_3373_, lean_object* v_logExceptions_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
uint8_t v_logExceptions_boxed_3379_; lean_object* v_res_3380_; 
v_logExceptions_boxed_3379_ = lean_unbox(v_logExceptions_3374_);
v_res_3380_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3372_, v_init_3373_, v_logExceptions_boxed_3379_, v_a_3375_, v_a_3376_, v_a_3377_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec_ref(v_a_3375_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_cfg_3381_, lean_object* v_init_3382_, uint8_t v_logExceptions_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_cfg_3381_, v_init_3382_, v_logExceptions_3383_, v_a_3384_, v_a_3390_, v_a_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_cfg_3394_, lean_object* v_init_3395_, lean_object* v_logExceptions_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
uint8_t v_logExceptions_boxed_3406_; lean_object* v_res_3407_; 
v_logExceptions_boxed_3406_ = lean_unbox(v_logExceptions_3396_);
v_res_3407_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_cfg_3394_, v_init_3395_, v_logExceptions_boxed_3406_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
return v_res_3407_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_3422_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_3421_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v_x_3423_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3436_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = l_Lean_MVarId_liftLets(v_a_3445_, v_a_3434_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3449_, v___y_3436_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_a_3451_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3446_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3446_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_a_3434_);
v_a_3459_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3444_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3444_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_3500_, lean_object* v_a_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3503_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_3512_, v_h_3500_, v_a_3501_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_a_3514_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3516_, v___y_3503_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3517_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_a_3518_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3513_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3513_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_a_3501_);
lean_dec(v_h_3500_);
v_a_3526_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3511_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3511_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_3534_, lean_object* v_a_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_3534_, v_a_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_3546_, lean_object* v_h_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___f_3557_; lean_object* v___x_3558_; 
v___f_3557_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3557_, 0, v_h_3547_);
lean_closure_set(v___f_3557_, 1, v_a_3546_);
v___x_3558_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3557_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_3559_, lean_object* v_h_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_3559_, v_h_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_3578_);
v___x_3605_ = l_Lean_Syntax_isOfKind(v_x_3578_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec(v_x_3578_);
v___x_3606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3606_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = l_Lean_Syntax_getArg(v_x_3578_, v___x_3607_);
v___x_3609_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_3608_);
v___x_3610_ = l_Lean_Syntax_isOfKind(v___x_3608_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec(v___x_3608_);
lean_dec(v_x_3578_);
v___x_3611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3611_;
}
else
{
lean_object* v___f_3612_; lean_object* v_loc_x3f_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___f_3612_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_3647_ = lean_unsigned_to_nat(2u);
v___x_3648_ = l_Lean_Syntax_getArg(v_x_3578_, v___x_3647_);
lean_dec(v_x_3578_);
v___x_3649_ = l_Lean_Syntax_isNone(v___x_3648_);
if (v___x_3649_ == 0)
{
uint8_t v___x_3650_; 
lean_inc(v___x_3648_);
v___x_3650_ = l_Lean_Syntax_matchesNull(v___x_3648_, v___x_3607_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec(v___x_3648_);
lean_dec(v___x_3608_);
v___x_3651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; lean_object* v_loc_x3f_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3652_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3653_ = l_Lean_Syntax_getArg(v___x_3648_, v___x_3652_);
lean_dec(v___x_3648_);
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3653_);
v___x_3655_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; 
lean_dec(v_loc_x3f_3653_);
lean_dec(v___x_3608_);
v___x_3656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3656_;
}
else
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_loc_x3f_3653_);
v_loc_x3f_3614_ = v___x_3657_;
v___y_3615_ = v_a_3579_;
v___y_3616_ = v_a_3580_;
v___y_3617_ = v_a_3581_;
v___y_3618_ = v_a_3582_;
v___y_3619_ = v_a_3583_;
v___y_3620_ = v_a_3584_;
v___y_3621_ = v_a_3585_;
v___y_3622_ = v_a_3586_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v___x_3658_; 
lean_dec(v___x_3648_);
v___x_3658_ = lean_box(0);
v_loc_x3f_3614_ = v___x_3658_;
v___y_3615_ = v_a_3579_;
v___y_3616_ = v_a_3580_;
v___y_3617_ = v_a_3581_;
v___y_3618_ = v_a_3582_;
v___y_3619_ = v_a_3583_;
v___y_3620_ = v_a_3584_;
v___y_3621_ = v_a_3585_;
v___y_3622_ = v_a_3586_;
goto v___jp_3613_;
}
v___jp_3613_:
{
uint8_t v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3623_ = 0;
v___x_3624_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_3624_, 0, v___x_3623_);
lean_ctor_set_uint8(v___x_3624_, 1, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 2, v___x_3623_);
lean_ctor_set_uint8(v___x_3624_, 3, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 4, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 5, v___x_3623_);
lean_ctor_set_uint8(v___x_3624_, 6, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 7, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 8, v___x_3623_);
lean_ctor_set_uint8(v___x_3624_, 9, v___x_3610_);
lean_ctor_set_uint8(v___x_3624_, 10, v___x_3610_);
v___x_3625_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_3608_, v___x_3624_, v___x_3610_, v___y_3615_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___f_3629_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc_n(v_a_3626_, 2);
lean_dec_ref_known(v___x_3625_, 1);
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3627_, 0, v_a_3626_);
v___f_3628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3628_, 0, v___f_3627_);
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_3629_, 0, v_a_3626_);
if (lean_obj_tag(v_loc_x3f_3614_) == 0)
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_box(0);
v___y_3589_ = v___f_3628_;
v___y_3590_ = v___y_3615_;
v___y_3591_ = v___y_3618_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3616_;
v___y_3594_ = v___y_3622_;
v___y_3595_ = v___f_3612_;
v___y_3596_ = v___y_3621_;
v___y_3597_ = v___y_3619_;
v___y_3598_ = v___f_3629_;
v___y_3599_ = v___y_3617_;
v___y_3600_ = v___x_3630_;
goto v___jp_3588_;
}
else
{
lean_object* v_val_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
v_val_3631_ = lean_ctor_get(v_loc_x3f_3614_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_loc_x3f_3614_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v_loc_x3f_3614_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_val_3631_);
lean_dec(v_loc_x3f_3614_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_val_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
v___y_3589_ = v___f_3628_;
v___y_3590_ = v___y_3615_;
v___y_3591_ = v___y_3618_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3616_;
v___y_3594_ = v___y_3622_;
v___y_3595_ = v___f_3612_;
v___y_3596_ = v___y_3621_;
v___y_3597_ = v___y_3619_;
v___y_3598_ = v___f_3629_;
v___y_3599_ = v___y_3617_;
v___y_3600_ = v___x_3636_;
goto v___jp_3588_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec(v_loc_x3f_3614_);
v_a_3639_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3625_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3625_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
v___jp_3588_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = l_Lean_mkOptionalNode(v___y_3600_);
v___x_3602_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3601_);
lean_dec(v___x_3601_);
lean_inc_ref(v___y_3595_);
v___x_3603_ = l_Lean_Elab_Tactic_withLocation(v___x_3602_, v___y_3598_, v___y_3589_, v___y_3595_, v___y_3590_, v___y_3593_, v___y_3599_, v___y_3591_, v___y_3597_, v___y_3592_, v___y_3596_, v___y_3594_);
lean_dec(v___x_3602_);
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3677_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3678_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_3679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_3680_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_3681_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3677_, v___x_3678_, v___x_3679_, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_3683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_3698_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_3697_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v_x_3699_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t v___x_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3712_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = l_Lean_MVarId_letToHave(v_a_3721_, v___x_3710_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = lean_box(0);
v___x_3725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_a_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3725_, v___y_3712_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3726_;
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
v_a_3727_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3722_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3722_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3720_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3720_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v___x_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
uint8_t v___x_1775__boxed_3753_; lean_object* v_res_3754_; 
v___x_1775__boxed_3753_ = lean_unbox(v___x_3743_);
v_res_3754_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v___x_1775__boxed_3753_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object* v_h_3755_, uint8_t v___x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3758_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3768_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_3767_, v_h_3755_, v___x_3756_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3768_, 1);
v___x_3770_ = lean_box(0);
v___x_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3771_, v___y_3758_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
return v___x_3772_;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3768_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3768_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_h_3755_);
v_a_3781_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3766_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3766_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v_h_3789_, lean_object* v___x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
uint8_t v___x_1851__boxed_3800_; lean_object* v_res_3801_; 
v___x_1851__boxed_3800_ = lean_unbox(v___x_3790_);
v_res_3801_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v_h_3789_, v___x_1851__boxed_3800_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_3802_, lean_object* v_h_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v___f_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_box(v___x_3802_);
v___f_3814_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 11, 2);
lean_closure_set(v___f_3814_, 0, v_h_3803_);
lean_closure_set(v___f_3814_, 1, v___x_3813_);
v___x_3815_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3814_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_3816_, lean_object* v_h_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v___x_1927__boxed_3827_; lean_object* v_res_3828_; 
v___x_1927__boxed_3827_ = lean_unbox(v___x_3816_);
v_res_3828_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1927__boxed_3827_, v_h_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3846_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_3836_);
v___x_3847_ = l_Lean_Syntax_isOfKind(v_x_3836_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_dec(v_x_3836_);
v___x_3848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3848_;
}
else
{
lean_object* v___f_3849_; lean_object* v___x_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___f_3854_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___f_3849_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_3850_ = lean_box(v___x_3847_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3851_, 0, v___x_3850_);
v___f_3852_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3852_, 0, v___f_3851_);
v___x_3853_ = lean_box(v___x_3847_);
v___f_3854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_3854_, 0, v___x_3853_);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v_x_3836_, v___x_3868_);
lean_dec(v_x_3836_);
v___x_3870_ = l_Lean_Syntax_isNone(v___x_3869_);
if (v___x_3870_ == 0)
{
uint8_t v___x_3871_; 
lean_inc(v___x_3869_);
v___x_3871_ = l_Lean_Syntax_matchesNull(v___x_3869_, v___x_3868_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_dec(v___x_3869_);
lean_dec_ref(v___f_3854_);
lean_dec_ref(v___f_3852_);
v___x_3872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3872_;
}
else
{
lean_object* v___x_3873_; lean_object* v_loc_x3f_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v_loc_x3f_3874_ = l_Lean_Syntax_getArg(v___x_3869_, v___x_3873_);
lean_dec(v___x_3869_);
v___x_3875_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_3874_);
v___x_3876_ = l_Lean_Syntax_isOfKind(v_loc_x3f_3874_, v___x_3875_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; 
lean_dec(v_loc_x3f_3874_);
lean_dec_ref(v___f_3854_);
lean_dec_ref(v___f_3852_);
v___x_3877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_3877_;
}
else
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_loc_x3f_3874_);
v___y_3856_ = v_a_3844_;
v___y_3857_ = v_a_3841_;
v___y_3858_ = v_a_3843_;
v___y_3859_ = v_a_3839_;
v___y_3860_ = v_a_3840_;
v___y_3861_ = v_a_3838_;
v___y_3862_ = v_a_3842_;
v___y_3863_ = v_a_3837_;
v___y_3864_ = v___x_3878_;
goto v___jp_3855_;
}
}
}
else
{
lean_object* v___x_3879_; 
lean_dec(v___x_3869_);
v___x_3879_ = lean_box(0);
v___y_3856_ = v_a_3844_;
v___y_3857_ = v_a_3841_;
v___y_3858_ = v_a_3843_;
v___y_3859_ = v_a_3839_;
v___y_3860_ = v_a_3840_;
v___y_3861_ = v_a_3838_;
v___y_3862_ = v_a_3842_;
v___y_3863_ = v_a_3837_;
v___y_3864_ = v___x_3879_;
goto v___jp_3855_;
}
v___jp_3855_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = l_Lean_mkOptionalNode(v___y_3864_);
v___x_3866_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_3865_);
lean_dec(v___x_3865_);
v___x_3867_ = l_Lean_Elab_Tactic_withLocation(v___x_3866_, v___f_3854_, v___f_3852_, v___f_3849_, v___y_3863_, v___y_3861_, v___y_3859_, v___y_3860_, v___y_3857_, v___y_3862_, v___y_3858_, v___y_3856_);
lean_dec(v___x_3866_);
return v___x_3867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3898_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3899_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_3901_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_3902_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3898_, v___x_3899_, v___x_3900_, v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_3904_;
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
