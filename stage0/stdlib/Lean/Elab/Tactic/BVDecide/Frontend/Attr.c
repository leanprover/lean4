// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Attr
// Imports: public import Lean.Elab.Tactic.Simp public import Std.Tactic.BVDecide.Syntax import Lean.Elab.ConfigEval
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 168, 14, 82, 188, 236, 147, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 77, 173, 50, 9, 24, 54, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 61, 132, 134, 92, 229, 233, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 110, 67, 26, 14, 230, 237, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 59, 58, 26, 252, 129, 241, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 251, 73, 58, 48, 5, 178, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 45, 120, 6, 149, 92, 82, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 100, 1, 28, 14, 168, 229, 227)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 90, 154, 245, 99, 63, 152, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 159, 253, 92, 146, 69, 2, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 209, 15, 222, 36, 133, 231, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 144, 145, 193, 241, 173, 88, 141)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 6, 184, 147, 13, 84, 64, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 249, 59, 75, 64, 203, 31, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 15, 200, 94, 39, 211, 82, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 54, 76, 24, 63, 126, 31, 154)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 25, 212, 149, 63, 123, 50, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(921759773) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 243, 17, 184, 17, 126, 248, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 135, 235, 141, 78, 202, 134, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 90, 52, 184, 106, 21, 216, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 139, 203, 35, 161, 91, 82, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "solver"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 159, 50, 22, 96, 145, 4, 16)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 158, 105, 178, 36, 68, 6, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 500, .m_capacity = 500, .m_length = 499, .m_data = "Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n\n     1. If this is set to something besides the empty string they will use that binary.\n\n     2. If this is set to the empty string they will check if there is a cadical binary next to theexecuting program. Usually that program is going to be `lean` itself and we do ship a`cadical` next to it.\n\n     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicatesto use the one that ships with Lean."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 157, 42, 75, 34, 202, 38, 95)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 182, 7, 175, 119, 199, 66, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "counterexample"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "SolverMode"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___boxed, .m_arity = 15, .m_num_fixed = 6, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 20, 153, 227, 156, 77, 79, 25)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode;
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BVDecideConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "graphviz"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "solverMode"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeout"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "trimProofs"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 5, 175, 37, 242, 16, 58, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(115, 192, 245, 65, 78, 207, 150, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 166, 2, 46, 117, 68, 136, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 82, 64, 83, 196, 140, 93, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "shortCircuit"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 80, 103, 64, 204, 115, 204, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(80, 66, 92, 194, 212, 111, 180, 66)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(56, 108, 135, 82, 96, 255, 21, 14)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "embeddedConstraintSubst"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enums"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixedInt"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(135, 204, 117, 124, 201, 55, 171, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(165, 86, 123, 61, 127, 72, 118, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 17, 210, 81, 221, 49, 195, 119)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "acNf"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "andFlattening"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binaryProofs"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(157, 22, 250, 188, 85, 112, 209, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(27, 1, 185, 174, 248, 173, 50, 124)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(232, 188, 62, 72, 44, 63, 204, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "simp theorems used by bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bvNormalizeExt"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 26, 101, 129, 96, 146, 148, 11)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "simp theorems used to convert UIntX/IntX statements into BitVec ones"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "intToBitVecExt"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 200, 236, 49, 216, 88, 223, 50)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "bv_normalize_proc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 55, 180, 228, 60, 0, 67, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "simprocs used by bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bvNormalizeSimprocExt"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 161, 84, 53, 66, 95, 10, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected type at bv_normalize simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value),LEAN_SCALAR_PTR_LITERAL(236, 33, 85, 75, 207, 191, 2, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Not implemented yet, [-builtin_bv_normalize_proc]"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "addBVNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1596612692) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 50, 70, 134, 5, 67, 42, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 90, 82, 225, 212, 148, 134, 97)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 7, 177, 203, 127, 7, 203, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(231, 134, 121, 139, 58, 106, 105, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "bvNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 5, 36, 101, 149, 10, 160, 102)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Builtin bv_normalize simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_95_ = 0;
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_97_ = l_Lean_registerTraceClass(v___x_94_, v___x_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2____boxed(lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(3575118154u);
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_109_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_110_ = l_Lean_Name_str___override(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_112_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_113_ = l_Lean_Name_str___override(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_));
v___x_119_ = 0;
v___x_120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object* v_name_124_, lean_object* v_decl_125_, lean_object* v_ref_126_){
_start:
{
lean_object* v_defValue_128_; lean_object* v_descr_129_; lean_object* v_deprecation_x3f_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_defValue_128_ = lean_ctor_get(v_decl_125_, 0);
v_descr_129_ = lean_ctor_get(v_decl_125_, 1);
v_deprecation_x3f_130_ = lean_ctor_get(v_decl_125_, 2);
lean_inc(v_defValue_128_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_defValue_128_);
lean_inc(v_deprecation_x3f_130_);
lean_inc_ref(v_descr_129_);
lean_inc_n(v_name_124_, 2);
v___x_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_132_, 0, v_name_124_);
lean_ctor_set(v___x_132_, 1, v_ref_126_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
lean_ctor_set(v___x_132_, 3, v_descr_129_);
lean_ctor_set(v___x_132_, 4, v_deprecation_x3f_130_);
v___x_133_ = lean_register_option(v_name_124_, v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v___x_133_, 0);
lean_dec(v_unused_142_);
v___x_135_ = v___x_133_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_dec(v___x_133_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_inc(v_defValue_128_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_name_124_);
lean_ctor_set(v___x_137_, 1, v_defValue_128_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_name_124_);
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_151_, lean_object* v_decl_152_, lean_object* v_ref_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_151_, v_decl_152_, v_ref_153_);
lean_dec_ref(v_decl_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_178_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(v___x_175_, v___x_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0(lean_object* v_00_u03b1_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0(v_00_u03b1_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0(lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v_ctor_216_, lean_object* v_args_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_226_ = lean_string_dec_eq(v_ctor_216_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_228_ = lean_string_dec_eq(v_ctor_216_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_230_ = lean_string_dec_eq(v_ctor_216_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec_ref(v___x_215_);
lean_dec_ref(v___x_214_);
lean_dec_ref(v___x_213_);
lean_dec_ref(v___x_212_);
lean_dec_ref(v___x_211_);
lean_dec_ref(v___x_210_);
v___x_231_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = l_Lean_Name_mkStr7(v___x_210_, v___x_211_, v___x_212_, v___x_213_, v___x_214_, v___x_215_, v___x_229_);
v___x_233_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_232_);
v___x_234_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_232_, v___x_233_, v_args_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_234_, 0);
lean_dec(v_unused_247_);
v___x_236_ = v___x_234_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_234_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_238_ = 0;
v___x_239_ = lean_box(0);
v___x_240_ = l_Lean_Expr_const___override(v___x_232_, v___x_239_);
v___x_241_ = lean_box(v___x_238_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_242_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v___x_232_);
v_a_248_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_234_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_234_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = l_Lean_Name_mkStr7(v___x_210_, v___x_211_, v___x_212_, v___x_213_, v___x_214_, v___x_215_, v___x_227_);
v___x_257_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_256_);
v___x_258_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_256_, v___x_257_, v_args_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_270_; 
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_258_, 0);
lean_dec(v_unused_271_);
v___x_260_ = v___x_258_;
v_isShared_261_ = v_isSharedCheck_270_;
goto v_resetjp_259_;
}
else
{
lean_dec(v___x_258_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_270_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_262_ = 2;
v___x_263_ = lean_box(0);
v___x_264_ = l_Lean_Expr_const___override(v___x_256_, v___x_263_);
v___x_265_ = lean_box(v___x_262_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_266_);
v___x_268_ = v___x_260_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v___x_256_);
v_a_272_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_258_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_258_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_Name_mkStr7(v___x_210_, v___x_211_, v___x_212_, v___x_213_, v___x_214_, v___x_215_, v___x_225_);
v___x_281_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_280_);
v___x_282_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_280_, v___x_281_, v_args_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_294_; 
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_295_);
v___x_284_ = v___x_282_;
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_282_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_286_ = 1;
v___x_287_ = lean_box(0);
v___x_288_ = l_Lean_Expr_const___override(v___x_280_, v___x_287_);
v___x_289_ = lean_box(v___x_286_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_290_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v___x_280_);
v_a_296_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_282_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_282_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object* v___x_304_, lean_object* v___x_305_, lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v___x_308_, lean_object* v___x_309_, lean_object* v_ctor_310_, lean_object* v_args_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0(v___x_304_, v___x_305_, v___x_306_, v___x_307_, v___x_308_, v___x_309_, v_ctor_310_, v_args_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v_args_311_);
lean_dec_ref(v_ctor_310_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___f_343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__1));
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2));
v___x_345_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_344_, v___f_343_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___boxed(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm(v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
return v_res_354_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_box(0);
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2));
v___x_358_ = l_Lean_Expr_const___override(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1);
v___x_360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__0));
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__2);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0(lean_object* v_00_u03b1_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0(v_00_u03b1_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object* v_msgData_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v_env_392_; lean_object* v___x_393_; lean_object* v_mctx_394_; lean_object* v_lctx_395_; lean_object* v_options_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_391_ = lean_st_ref_get(v___y_389_);
v_env_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc_ref(v_env_392_);
lean_dec(v___x_391_);
v___x_393_ = lean_st_ref_get(v___y_387_);
v_mctx_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_mctx_394_);
lean_dec(v___x_393_);
v_lctx_395_ = lean_ctor_get(v___y_386_, 2);
v_options_396_ = lean_ctor_get(v___y_388_, 2);
lean_inc_ref(v_options_396_);
lean_inc_ref(v_lctx_395_);
v___x_397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_397_, 0, v_env_392_);
lean_ctor_set(v___x_397_, 1, v_mctx_394_);
lean_ctor_set(v___x_397_, 2, v_lctx_395_);
lean_ctor_set(v___x_397_, 3, v_options_396_);
v___x_398_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_msgData_385_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_ref_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_ref_413_ = lean_ctor_get(v___y_410_, 5);
v___x_414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc(v_ref_413_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_ref_413_);
lean_ctor_set(v___x_419_, 1, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 1);
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_434_, lean_object* v_args_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_454_ = lean_string_dec_eq(v_ctor_434_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_456_ = lean_string_dec_eq(v_ctor_434_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_458_ = lean_string_dec_eq(v_ctor_434_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_array_get_size(v_args_435_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_nat_dec_eq(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v___x_463_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_464_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_463_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
goto v___jp_441_;
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_array_get_size(v_args_435_);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v___x_476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_477_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_476_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_array_get_size(v_args_435_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_489_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
goto v___jp_449_;
}
}
v___jp_441_:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = 0;
v___x_443_ = lean_box(v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
v___jp_445_:
{
uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = 2;
v___x_447_ = lean_box(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
v___jp_449_:
{
uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = 1;
v___x_451_ = lean_box(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_499_, lean_object* v_args_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_499_, v_args_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v_args_500_);
lean_dec_ref(v_ctor_499_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr(lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___f_514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___closed__0));
v___x_515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm___closed__2));
v___x_516_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_515_, v___f_514_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr(v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_524_, lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_532_, v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1);
v___x_544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__0));
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__2);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v_ctor_548_, lean_object* v_args_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_733_ = lean_string_dec_eq(v_ctor_548_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_array_get_size(v_args_549_);
v___x_736_ = lean_unsigned_to_nat(13u);
v___x_737_ = lean_nat_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v___x_738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_739_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_738_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
goto v___jp_555_;
}
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = l_Lean_instInhabitedExpr;
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_557_);
lean_inc(v___x_558_);
v___x_559_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_558_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_561_);
lean_inc(v___x_562_);
v___x_563_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_562_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = lean_unsigned_to_nat(2u);
v___x_566_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_565_);
lean_inc(v___x_566_);
v___x_567_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_566_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_569_);
lean_inc(v___x_570_);
v___x_571_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_570_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_unsigned_to_nat(4u);
v___x_574_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_573_);
lean_inc(v___x_574_);
v___x_575_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_574_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = lean_unsigned_to_nat(5u);
v___x_578_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_577_);
lean_inc(v___x_578_);
v___x_579_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_578_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_unsigned_to_nat(6u);
v___x_582_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_581_);
lean_inc(v___x_582_);
v___x_583_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_582_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_unsigned_to_nat(7u);
v___x_586_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_585_);
lean_inc(v___x_586_);
v___x_587_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_586_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_unsigned_to_nat(8u);
v___x_590_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_589_);
lean_inc(v___x_590_);
v___x_591_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_590_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = lean_unsigned_to_nat(9u);
v___x_594_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_593_);
lean_inc(v___x_594_);
v___x_595_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_594_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_unsigned_to_nat(10u);
v___x_598_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_597_);
lean_inc(v___x_598_);
v___x_599_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_598_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unsigned_to_nat(11u);
v___x_602_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_601_);
lean_inc(v___x_602_);
v___x_603_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_602_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = lean_unsigned_to_nat(12u);
v___x_606_ = lean_array_get_borrowed(v___x_556_, v_args_549_, v___x_605_);
lean_inc(v___x_606_);
v___x_607_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr(v___x_606_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_627_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; uint8_t v___x_613_; uint8_t v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; uint8_t v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_625_; 
v___x_612_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_612_, 0, v_a_560_);
lean_ctor_set(v___x_612_, 1, v_a_600_);
v___x_613_ = lean_unbox(v_a_564_);
lean_dec(v_a_564_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2, v___x_613_);
v___x_614_ = lean_unbox(v_a_568_);
lean_dec(v_a_568_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 1, v___x_614_);
v___x_615_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 2, v___x_615_);
v___x_616_ = lean_unbox(v_a_576_);
lean_dec(v_a_576_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 3, v___x_616_);
v___x_617_ = lean_unbox(v_a_580_);
lean_dec(v_a_580_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 4, v___x_617_);
v___x_618_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 5, v___x_618_);
v___x_619_ = lean_unbox(v_a_588_);
lean_dec(v_a_588_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 6, v___x_619_);
v___x_620_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 7, v___x_620_);
v___x_621_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 8, v___x_621_);
v___x_622_ = lean_unbox(v_a_604_);
lean_dec(v_a_604_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 9, v___x_622_);
v___x_623_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*2 + 10, v___x_623_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_625_ = v___x_610_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_612_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_604_);
lean_dec(v_a_600_);
lean_dec(v_a_596_);
lean_dec(v_a_592_);
lean_dec(v_a_588_);
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_628_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_607_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_607_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_a_600_);
lean_dec(v_a_596_);
lean_dec(v_a_592_);
lean_dec(v_a_588_);
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_636_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_603_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_603_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_a_596_);
lean_dec(v_a_592_);
lean_dec(v_a_588_);
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_644_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_599_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_599_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_592_);
lean_dec(v_a_588_);
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_652_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_595_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_595_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_a_588_);
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_660_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_591_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_591_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_a_584_);
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_668_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_587_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_587_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_a_580_);
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_676_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_583_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_583_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_684_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_579_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_579_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_692_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_575_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_575_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_a_568_);
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_700_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_571_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_571_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_564_);
lean_dec(v_a_560_);
v_a_708_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_567_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_567_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_a_560_);
v_a_716_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_563_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_563_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_a_724_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_559_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_559_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_748_, lean_object* v_args_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___lam__0(v_ctor_748_, v_args_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v_args_749_);
lean_dec_ref(v_ctor_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___f_771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__0));
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_773_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_772_, v___f_771_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr(v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_784_ = l_Lean_Expr_const___override(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2);
v___x_788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__0));
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__3);
return v___x_790_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(1);
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_797_ = l_Lean_MessageData_ofFormat(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
return v_x_798_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_823_; 
v_head_800_ = lean_ctor_get(v_x_799_, 0);
v_tail_801_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_823_ == 0)
{
v___x_803_ = v_x_799_;
v_isShared_804_ = v_isSharedCheck_823_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_tail_801_);
lean_inc(v_head_800_);
lean_dec(v_x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_823_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_before_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_821_; 
v_before_805_ = lean_ctor_get(v_head_800_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_head_800_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_head_800_, 1);
lean_dec(v_unused_822_);
v___x_807_ = v_head_800_;
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_before_805_);
lean_dec(v_head_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 7);
lean_ctor_set(v___x_807_, 1, v___x_809_);
lean_ctor_set(v___x_807_, 0, v_x_798_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_x_798_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_820_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 7);
lean_ctor_set(v___x_803_, 1, v___x_812_);
lean_ctor_set(v___x_803_, 0, v___x_811_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_MessageData_ofSyntax(v_before_805_);
v___x_816_ = l_Lean_indentD(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v_x_798_ = v___x_817_;
v_x_799_ = v_tail_801_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_824_, lean_object* v_opt_825_){
_start:
{
lean_object* v_name_826_; lean_object* v_defValue_827_; lean_object* v_map_828_; lean_object* v___x_829_; 
v_name_826_ = lean_ctor_get(v_opt_825_, 0);
v_defValue_827_ = lean_ctor_get(v_opt_825_, 1);
v_map_828_ = lean_ctor_get(v_opts_824_, 0);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_828_, v_name_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
uint8_t v___x_830_; 
v___x_830_ = lean_unbox(v_defValue_827_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_829_, 1);
if (lean_obj_tag(v_val_831_) == 1)
{
uint8_t v_v_832_; 
v_v_832_ = lean_ctor_get_uint8(v_val_831_, 0);
lean_dec_ref_known(v_val_831_, 0);
return v_v_832_;
}
else
{
uint8_t v___x_833_; 
lean_dec(v_val_831_);
v___x_833_ = lean_unbox(v_defValue_827_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_834_, lean_object* v_opt_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_834_, v_opt_835_);
lean_dec_ref(v_opt_835_);
lean_dec_ref(v_opts_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_842_ = l_Lean_MessageData_ofFormat(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_843_, lean_object* v_macroStack_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_options_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_options_847_ = lean_ctor_get(v___y_845_, 2);
v___x_848_ = l_Lean_Elab_pp_macroStack;
v___x_849_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_options_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_macroStack_844_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_msgData_843_);
return v___x_850_;
}
else
{
if (lean_obj_tag(v_macroStack_844_) == 0)
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_msgData_843_);
return v___x_851_;
}
else
{
lean_object* v_head_852_; lean_object* v_after_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_868_; 
v_head_852_ = lean_ctor_get(v_macroStack_844_, 0);
lean_inc(v_head_852_);
v_after_853_ = lean_ctor_get(v_head_852_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_head_852_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_head_852_, 0);
lean_dec(v_unused_869_);
v___x_855_ = v_head_852_;
v_isShared_856_ = v_isSharedCheck_868_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_after_853_);
lean_dec(v_head_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_868_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 7);
lean_ctor_set(v___x_855_, 1, v___x_857_);
lean_ctor_set(v___x_855_, 0, v_msgData_843_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_msgData_843_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_867_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_msgData_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_860_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_MessageData_ofSyntax(v_after_853_);
v___x_863_ = l_Lean_indentD(v___x_862_);
v_msgData_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_864_, 0, v___x_861_);
lean_ctor_set(v_msgData_864_, 1, v___x_863_);
v___x_865_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_864_, v_macroStack_844_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_870_, lean_object* v_macroStack_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_870_, v_macroStack_871_, v___y_872_);
lean_dec_ref(v___y_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v_macroStack_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
v_ref_883_ = lean_ctor_get(v___y_880_, 5);
v___x_884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_875_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v_macroStack_886_ = lean_ctor_get(v___y_876_, 1);
v___x_887_ = l_Lean_Elab_getBetterRef(v_ref_883_, v_macroStack_886_);
lean_inc(v_macroStack_886_);
v___x_888_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_885_, v_macroStack_886_, v___y_880_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_887_);
lean_ctor_set(v___x_893_, 1, v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 1);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_906_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_box(0);
v___x_908_ = l_Lean_Elab_abortTermExceptionId;
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_915_, lean_object* v___y_916_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_Expr_hasMVar(v_e_915_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_e_915_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v_mctx_921_; lean_object* v___x_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_925_; lean_object* v_cache_926_; lean_object* v_zetaDeltaFVarIds_927_; lean_object* v_postponed_928_; lean_object* v_diag_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_938_; 
v___x_920_ = lean_st_ref_get(v___y_916_);
v_mctx_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_mctx_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_instantiateMVarsCore(v_mctx_921_, v_e_915_);
v_fst_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_fst_923_);
v_snd_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_snd_924_);
lean_dec_ref(v___x_922_);
v___x_925_ = lean_st_ref_take(v___y_916_);
v_cache_926_ = lean_ctor_get(v___x_925_, 1);
v_zetaDeltaFVarIds_927_ = lean_ctor_get(v___x_925_, 2);
v_postponed_928_ = lean_ctor_get(v___x_925_, 3);
v_diag_929_ = lean_ctor_get(v___x_925_, 4);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_939_);
v___x_931_ = v___x_925_;
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_diag_929_);
lean_inc(v_postponed_928_);
lean_inc(v_zetaDeltaFVarIds_927_);
lean_inc(v_cache_926_);
lean_dec(v___x_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_snd_924_);
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_snd_924_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_cache_926_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_zetaDeltaFVarIds_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_postponed_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_diag_929_);
v___x_934_ = v_reuseFailAlloc_937_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_st_ref_set(v___y_916_, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_fst_923_);
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_940_, v___y_941_);
lean_dec(v___y_941_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__1);
v___x_948_ = l_Lean_MessageData_ofExpr(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_950_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_956_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_ty_x3f_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_fileName_978_; lean_object* v_fileMap_979_; lean_object* v_options_980_; lean_object* v_currRecDepth_981_; lean_object* v_maxRecDepth_982_; lean_object* v_ref_983_; lean_object* v_currNamespace_984_; lean_object* v_openDecls_985_; lean_object* v_initHeartbeats_986_; lean_object* v_maxHeartbeats_987_; lean_object* v_quotContext_988_; lean_object* v_currMacroScope_989_; uint8_t v_diag_990_; lean_object* v_cancelTk_x3f_991_; uint8_t v_suppressElabErrors_992_; lean_object* v_inheritedTraceOptions_993_; uint8_t v___x_994_; lean_object* v_ref_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_ty_x3f_972_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig___closed__2);
v___x_973_ = 1;
v___x_974_ = lean_box(0);
v___x_975_ = lean_box(v___x_973_);
v___x_976_ = lean_box(v___x_973_);
lean_inc(v_stx_964_);
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_977_, 0, v_stx_964_);
lean_closure_set(v___x_977_, 1, v_ty_x3f_972_);
lean_closure_set(v___x_977_, 2, v___x_975_);
lean_closure_set(v___x_977_, 3, v___x_976_);
lean_closure_set(v___x_977_, 4, v___x_974_);
v_fileName_978_ = lean_ctor_get(v_a_969_, 0);
v_fileMap_979_ = lean_ctor_get(v_a_969_, 1);
v_options_980_ = lean_ctor_get(v_a_969_, 2);
v_currRecDepth_981_ = lean_ctor_get(v_a_969_, 3);
v_maxRecDepth_982_ = lean_ctor_get(v_a_969_, 4);
v_ref_983_ = lean_ctor_get(v_a_969_, 5);
v_currNamespace_984_ = lean_ctor_get(v_a_969_, 6);
v_openDecls_985_ = lean_ctor_get(v_a_969_, 7);
v_initHeartbeats_986_ = lean_ctor_get(v_a_969_, 8);
v_maxHeartbeats_987_ = lean_ctor_get(v_a_969_, 9);
v_quotContext_988_ = lean_ctor_get(v_a_969_, 10);
v_currMacroScope_989_ = lean_ctor_get(v_a_969_, 11);
v_diag_990_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*14);
v_cancelTk_x3f_991_ = lean_ctor_get(v_a_969_, 12);
v_suppressElabErrors_992_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_993_ = lean_ctor_get(v_a_969_, 13);
v___x_994_ = 1;
v_ref_995_ = l_Lean_replaceRef(v_stx_964_, v_ref_983_);
lean_dec(v_stx_964_);
lean_inc_ref(v_inheritedTraceOptions_993_);
lean_inc(v_cancelTk_x3f_991_);
lean_inc(v_currMacroScope_989_);
lean_inc(v_quotContext_988_);
lean_inc(v_maxHeartbeats_987_);
lean_inc(v_initHeartbeats_986_);
lean_inc(v_openDecls_985_);
lean_inc(v_currNamespace_984_);
lean_inc(v_maxRecDepth_982_);
lean_inc(v_currRecDepth_981_);
lean_inc_ref(v_options_980_);
lean_inc_ref(v_fileMap_979_);
lean_inc_ref(v_fileName_978_);
v___x_996_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_996_, 0, v_fileName_978_);
lean_ctor_set(v___x_996_, 1, v_fileMap_979_);
lean_ctor_set(v___x_996_, 2, v_options_980_);
lean_ctor_set(v___x_996_, 3, v_currRecDepth_981_);
lean_ctor_set(v___x_996_, 4, v_maxRecDepth_982_);
lean_ctor_set(v___x_996_, 5, v_ref_995_);
lean_ctor_set(v___x_996_, 6, v_currNamespace_984_);
lean_ctor_set(v___x_996_, 7, v_openDecls_985_);
lean_ctor_set(v___x_996_, 8, v_initHeartbeats_986_);
lean_ctor_set(v___x_996_, 9, v_maxHeartbeats_987_);
lean_ctor_set(v___x_996_, 10, v_quotContext_988_);
lean_ctor_set(v___x_996_, 11, v_currMacroScope_989_);
lean_ctor_set(v___x_996_, 12, v_cancelTk_x3f_991_);
lean_ctor_set(v___x_996_, 13, v_inheritedTraceOptions_993_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*14, v_diag_990_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*14 + 1, v_suppressElabErrors_992_);
v___x_997_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_977_, v___x_994_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v___x_996_, v_a_970_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v___y_1011_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; uint8_t v___x_1095_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_998_, v_a_968_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1095_ = l_Lean_Expr_hasSorry(v_a_1000_);
if (v___x_1095_ == 0)
{
v___y_1040_ = v_a_965_;
v___y_1041_ = v_a_966_;
v___y_1042_ = v_a_967_;
v___y_1043_ = v_a_968_;
v___y_1044_ = v___x_996_;
v___y_1045_ = v_a_970_;
goto v___jp_1039_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_Expr_hasSyntheticSorry(v_a_1000_);
if (v___x_1096_ == 0)
{
v___y_1077_ = v_a_965_;
v___y_1078_ = v_a_966_;
v___y_1079_ = v_a_967_;
v___y_1080_ = v_a_968_;
v___y_1081_ = v___x_996_;
v___y_1082_ = v_a_970_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1097_; lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_a_1000_);
lean_dec_ref_known(v___x_996_, 14);
v___x_1097_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1001_:
{
if (v___y_1011_ == 0)
{
if (lean_obj_tag(v___y_1005_) == 0)
{
lean_dec_ref_known(v___y_1005_, 2);
lean_dec_ref(v___y_1004_);
lean_dec(v_a_1000_);
return v___y_1002_;
}
else
{
lean_object* v_id_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1025_; 
v_id_1012_ = lean_ctor_get(v___y_1005_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___y_1005_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___y_1005_, 1);
lean_dec(v_unused_1026_);
v___x_1014_ = v___y_1005_;
v_isShared_1015_ = v_isSharedCheck_1025_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_id_1012_);
lean_dec(v___y_1005_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1025_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
uint8_t v___x_1016_; 
v___x_1016_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1008_, v_id_1012_);
lean_dec(v_id_1012_);
if (v___x_1016_ == 0)
{
lean_del_object(v___x_1014_);
lean_dec_ref(v___y_1004_);
lean_dec(v_a_1000_);
return v___y_1002_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec_ref(v___y_1002_);
v___x_1017_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_1018_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1019_ = l_Lean_indentExpr(v_a_1000_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 7);
lean_ctor_set(v___x_1014_, 1, v___x_1019_);
lean_ctor_set(v___x_1014_, 0, v___x_1018_);
v___x_1021_ = v___x_1014_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1017_);
v___x_1023_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1022_, v___y_1010_, v___y_1003_, v___y_1006_, v___y_1007_, v___y_1004_, v___y_1009_);
lean_dec_ref(v___y_1004_);
return v___x_1023_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v_a_1000_);
return v___y_1002_;
}
}
v___jp_1027_:
{
lean_object* v___x_1034_; 
lean_inc(v_a_1000_);
v___x_1034_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr(v_a_1000_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref(v___y_1032_);
lean_dec(v_a_1000_);
return v___x_1034_;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
v___x_1036_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1037_ = l_Lean_Exception_isInterrupt(v_a_1035_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; 
lean_inc(v_a_1035_);
v___x_1038_ = l_Lean_Exception_isRuntime(v_a_1035_);
v___y_1002_ = v___x_1034_;
v___y_1003_ = v___y_1029_;
v___y_1004_ = v___y_1032_;
v___y_1005_ = v_a_1035_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v___y_1031_;
v___y_1008_ = v___x_1036_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v___y_1028_;
v___y_1011_ = v___x_1038_;
goto v___jp_1001_;
}
else
{
v___y_1002_ = v___x_1034_;
v___y_1003_ = v___y_1029_;
v___y_1004_ = v___y_1032_;
v___y_1005_ = v_a_1035_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v___y_1031_;
v___y_1008_ = v___x_1036_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v___y_1028_;
v___y_1011_ = v___x_1037_;
goto v___jp_1001_;
}
}
}
v___jp_1039_:
{
lean_object* v___x_1046_; 
lean_inc(v_a_1000_);
v___x_1046_ = l_Lean_Meta_getMVars(v_a_1000_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1047_, v___x_974_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v_a_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; uint8_t v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = lean_unbox(v_a_1049_);
lean_dec(v_a_1049_);
if (v___x_1050_ == 0)
{
v___y_1028_ = v___y_1040_;
v___y_1029_ = v___y_1041_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1043_;
v___y_1032_ = v___y_1044_;
v___y_1033_ = v___y_1045_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v___y_1044_);
lean_dec(v_a_1000_);
v___x_1051_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v___y_1044_);
lean_dec(v_a_1000_);
v_a_1060_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1048_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1048_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___y_1044_);
lean_dec(v_a_1000_);
v_a_1068_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1046_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1046_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
v___jp_1076_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v___x_1083_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1084_ = l_Lean_indentExpr(v_a_1000_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1085_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec_ref(v___y_1081_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref_known(v___x_996_, 14);
v_a_1106_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_997_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_997_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1122_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1128_ = l_Lean_mkConst(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v_ty_x3f_1130_; 
v___x_1129_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1130_, 0, v___x_1129_);
return v_ty_x3f_1130_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1132_ = l_Lean_MessageData_ofExpr(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1134_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1137_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_ty_x3f_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_fileName_1153_; lean_object* v_fileMap_1154_; lean_object* v_options_1155_; lean_object* v_currRecDepth_1156_; lean_object* v_maxRecDepth_1157_; lean_object* v_ref_1158_; lean_object* v_currNamespace_1159_; lean_object* v_openDecls_1160_; lean_object* v_initHeartbeats_1161_; lean_object* v_maxHeartbeats_1162_; lean_object* v_quotContext_1163_; lean_object* v_currMacroScope_1164_; uint8_t v_diag_1165_; lean_object* v_cancelTk_x3f_1166_; uint8_t v_suppressElabErrors_1167_; lean_object* v_inheritedTraceOptions_1168_; uint8_t v___x_1169_; lean_object* v_ref_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_ty_x3f_1147_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1148_ = 1;
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_box(v___x_1148_);
v___x_1151_ = lean_box(v___x_1148_);
lean_inc(v_stx_1139_);
v___x_1152_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1152_, 0, v_stx_1139_);
lean_closure_set(v___x_1152_, 1, v_ty_x3f_1147_);
lean_closure_set(v___x_1152_, 2, v___x_1150_);
lean_closure_set(v___x_1152_, 3, v___x_1151_);
lean_closure_set(v___x_1152_, 4, v___x_1149_);
v_fileName_1153_ = lean_ctor_get(v_a_1144_, 0);
v_fileMap_1154_ = lean_ctor_get(v_a_1144_, 1);
v_options_1155_ = lean_ctor_get(v_a_1144_, 2);
v_currRecDepth_1156_ = lean_ctor_get(v_a_1144_, 3);
v_maxRecDepth_1157_ = lean_ctor_get(v_a_1144_, 4);
v_ref_1158_ = lean_ctor_get(v_a_1144_, 5);
v_currNamespace_1159_ = lean_ctor_get(v_a_1144_, 6);
v_openDecls_1160_ = lean_ctor_get(v_a_1144_, 7);
v_initHeartbeats_1161_ = lean_ctor_get(v_a_1144_, 8);
v_maxHeartbeats_1162_ = lean_ctor_get(v_a_1144_, 9);
v_quotContext_1163_ = lean_ctor_get(v_a_1144_, 10);
v_currMacroScope_1164_ = lean_ctor_get(v_a_1144_, 11);
v_diag_1165_ = lean_ctor_get_uint8(v_a_1144_, sizeof(void*)*14);
v_cancelTk_x3f_1166_ = lean_ctor_get(v_a_1144_, 12);
v_suppressElabErrors_1167_ = lean_ctor_get_uint8(v_a_1144_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1168_ = lean_ctor_get(v_a_1144_, 13);
v___x_1169_ = 1;
v_ref_1170_ = l_Lean_replaceRef(v_stx_1139_, v_ref_1158_);
lean_dec(v_stx_1139_);
lean_inc_ref(v_inheritedTraceOptions_1168_);
lean_inc(v_cancelTk_x3f_1166_);
lean_inc(v_currMacroScope_1164_);
lean_inc(v_quotContext_1163_);
lean_inc(v_maxHeartbeats_1162_);
lean_inc(v_initHeartbeats_1161_);
lean_inc(v_openDecls_1160_);
lean_inc(v_currNamespace_1159_);
lean_inc(v_maxRecDepth_1157_);
lean_inc(v_currRecDepth_1156_);
lean_inc_ref(v_options_1155_);
lean_inc_ref(v_fileMap_1154_);
lean_inc_ref(v_fileName_1153_);
v___x_1171_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1171_, 0, v_fileName_1153_);
lean_ctor_set(v___x_1171_, 1, v_fileMap_1154_);
lean_ctor_set(v___x_1171_, 2, v_options_1155_);
lean_ctor_set(v___x_1171_, 3, v_currRecDepth_1156_);
lean_ctor_set(v___x_1171_, 4, v_maxRecDepth_1157_);
lean_ctor_set(v___x_1171_, 5, v_ref_1170_);
lean_ctor_set(v___x_1171_, 6, v_currNamespace_1159_);
lean_ctor_set(v___x_1171_, 7, v_openDecls_1160_);
lean_ctor_set(v___x_1171_, 8, v_initHeartbeats_1161_);
lean_ctor_set(v___x_1171_, 9, v_maxHeartbeats_1162_);
lean_ctor_set(v___x_1171_, 10, v_quotContext_1163_);
lean_ctor_set(v___x_1171_, 11, v_currMacroScope_1164_);
lean_ctor_set(v___x_1171_, 12, v_cancelTk_x3f_1166_);
lean_ctor_set(v___x_1171_, 13, v_inheritedTraceOptions_1168_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*14, v_diag_1165_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*14 + 1, v_suppressElabErrors_1167_);
v___x_1172_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1152_, v___x_1169_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v___x_1171_, v_a_1145_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; uint8_t v___x_1270_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1173_, v_a_1143_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
v___x_1270_ = l_Lean_Expr_hasSorry(v_a_1175_);
if (v___x_1270_ == 0)
{
v___y_1215_ = v_a_1140_;
v___y_1216_ = v_a_1141_;
v___y_1217_ = v_a_1142_;
v___y_1218_ = v_a_1143_;
v___y_1219_ = v___x_1171_;
v___y_1220_ = v_a_1145_;
goto v___jp_1214_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Lean_Expr_hasSyntheticSorry(v_a_1175_);
if (v___x_1271_ == 0)
{
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
v___y_1254_ = v_a_1142_;
v___y_1255_ = v_a_1143_;
v___y_1256_ = v___x_1171_;
v___y_1257_ = v_a_1145_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1272_; lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1175_);
lean_dec_ref_known(v___x_1171_, 14);
v___x_1272_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
v___jp_1176_:
{
if (v___y_1186_ == 0)
{
if (lean_obj_tag(v___y_1183_) == 0)
{
lean_dec_ref_known(v___y_1183_, 2);
lean_dec_ref(v___y_1184_);
lean_dec(v_a_1175_);
return v___y_1182_;
}
else
{
lean_object* v_id_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1200_; 
v_id_1187_ = lean_ctor_get(v___y_1183_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___y_1183_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___y_1183_, 1);
lean_dec(v_unused_1201_);
v___x_1189_ = v___y_1183_;
v_isShared_1190_ = v_isSharedCheck_1200_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_id_1187_);
lean_dec(v___y_1183_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1200_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1178_, v_id_1187_);
lean_dec(v_id_1187_);
if (v___x_1191_ == 0)
{
lean_del_object(v___x_1189_);
lean_dec_ref(v___y_1184_);
lean_dec(v_a_1175_);
return v___y_1182_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec_ref(v___y_1182_);
v___x_1192_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1193_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1194_ = l_Lean_indentExpr(v_a_1175_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 7);
lean_ctor_set(v___x_1189_, 1, v___x_1194_);
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1192_);
v___x_1198_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1197_, v___y_1181_, v___y_1179_, v___y_1177_, v___y_1185_, v___y_1184_, v___y_1180_);
lean_dec_ref(v___y_1184_);
return v___x_1198_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1175_);
return v___y_1182_;
}
}
v___jp_1202_:
{
lean_object* v___x_1209_; 
lean_inc(v_a_1175_);
v___x_1209_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1175_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref(v___y_1207_);
lean_dec(v_a_1175_);
return v___x_1209_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
v___x_1211_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1212_ = l_Lean_Exception_isInterrupt(v_a_1210_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; 
lean_inc(v_a_1210_);
v___x_1213_ = l_Lean_Exception_isRuntime(v_a_1210_);
v___y_1177_ = v___y_1205_;
v___y_1178_ = v___x_1211_;
v___y_1179_ = v___y_1204_;
v___y_1180_ = v___y_1208_;
v___y_1181_ = v___y_1203_;
v___y_1182_ = v___x_1209_;
v___y_1183_ = v_a_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1206_;
v___y_1186_ = v___x_1213_;
goto v___jp_1176_;
}
else
{
v___y_1177_ = v___y_1205_;
v___y_1178_ = v___x_1211_;
v___y_1179_ = v___y_1204_;
v___y_1180_ = v___y_1208_;
v___y_1181_ = v___y_1203_;
v___y_1182_ = v___x_1209_;
v___y_1183_ = v_a_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1206_;
v___y_1186_ = v___x_1212_;
goto v___jp_1176_;
}
}
}
v___jp_1214_:
{
lean_object* v___x_1221_; 
lean_inc(v_a_1175_);
v___x_1221_ = l_Lean_Meta_getMVars(v_a_1175_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1222_, v___x_1149_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v_a_1222_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; uint8_t v___x_1225_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v___x_1225_ = lean_unbox(v_a_1224_);
lean_dec(v_a_1224_);
if (v___x_1225_ == 0)
{
v___y_1203_ = v___y_1215_;
v___y_1204_ = v___y_1216_;
v___y_1205_ = v___y_1217_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1219_;
v___y_1208_ = v___y_1220_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1175_);
v___x_1226_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1175_);
v_a_1235_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1223_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1223_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1175_);
v_a_1243_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1221_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1221_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1259_ = l_Lean_indentExpr(v_a_1175_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1260_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___y_1256_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref_known(v___x_1171_, 14);
v_a_1281_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1172_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1172_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_fileName_1306_; lean_object* v_fileMap_1307_; lean_object* v_options_1308_; lean_object* v_currRecDepth_1309_; lean_object* v_maxRecDepth_1310_; lean_object* v_ref_1311_; lean_object* v_currNamespace_1312_; lean_object* v_openDecls_1313_; lean_object* v_initHeartbeats_1314_; lean_object* v_maxHeartbeats_1315_; lean_object* v_quotContext_1316_; lean_object* v_currMacroScope_1317_; uint8_t v_diag_1318_; lean_object* v_cancelTk_x3f_1319_; uint8_t v_suppressElabErrors_1320_; lean_object* v_inheritedTraceOptions_1321_; lean_object* v_ref_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_fileName_1306_ = lean_ctor_get(v_a_1303_, 0);
v_fileMap_1307_ = lean_ctor_get(v_a_1303_, 1);
v_options_1308_ = lean_ctor_get(v_a_1303_, 2);
v_currRecDepth_1309_ = lean_ctor_get(v_a_1303_, 3);
v_maxRecDepth_1310_ = lean_ctor_get(v_a_1303_, 4);
v_ref_1311_ = lean_ctor_get(v_a_1303_, 5);
v_currNamespace_1312_ = lean_ctor_get(v_a_1303_, 6);
v_openDecls_1313_ = lean_ctor_get(v_a_1303_, 7);
v_initHeartbeats_1314_ = lean_ctor_get(v_a_1303_, 8);
v_maxHeartbeats_1315_ = lean_ctor_get(v_a_1303_, 9);
v_quotContext_1316_ = lean_ctor_get(v_a_1303_, 10);
v_currMacroScope_1317_ = lean_ctor_get(v_a_1303_, 11);
v_diag_1318_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*14);
v_cancelTk_x3f_1319_ = lean_ctor_get(v_a_1303_, 12);
v_suppressElabErrors_1320_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1321_ = lean_ctor_get(v_a_1303_, 13);
v_ref_1322_ = l_Lean_replaceRef(v_stx_1298_, v_ref_1311_);
lean_inc_ref(v_inheritedTraceOptions_1321_);
lean_inc(v_cancelTk_x3f_1319_);
lean_inc(v_currMacroScope_1317_);
lean_inc(v_quotContext_1316_);
lean_inc(v_maxHeartbeats_1315_);
lean_inc(v_initHeartbeats_1314_);
lean_inc(v_openDecls_1313_);
lean_inc(v_currNamespace_1312_);
lean_inc(v_maxRecDepth_1310_);
lean_inc(v_currRecDepth_1309_);
lean_inc_ref(v_options_1308_);
lean_inc_ref(v_fileMap_1307_);
lean_inc_ref(v_fileName_1306_);
v___x_1323_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1323_, 0, v_fileName_1306_);
lean_ctor_set(v___x_1323_, 1, v_fileMap_1307_);
lean_ctor_set(v___x_1323_, 2, v_options_1308_);
lean_ctor_set(v___x_1323_, 3, v_currRecDepth_1309_);
lean_ctor_set(v___x_1323_, 4, v_maxRecDepth_1310_);
lean_ctor_set(v___x_1323_, 5, v_ref_1322_);
lean_ctor_set(v___x_1323_, 6, v_currNamespace_1312_);
lean_ctor_set(v___x_1323_, 7, v_openDecls_1313_);
lean_ctor_set(v___x_1323_, 8, v_initHeartbeats_1314_);
lean_ctor_set(v___x_1323_, 9, v_maxHeartbeats_1315_);
lean_ctor_set(v___x_1323_, 10, v_quotContext_1316_);
lean_ctor_set(v___x_1323_, 11, v_currMacroScope_1317_);
lean_ctor_set(v___x_1323_, 12, v_cancelTk_x3f_1319_);
lean_ctor_set(v___x_1323_, 13, v_inheritedTraceOptions_1321_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*14, v_diag_1318_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*14 + 1, v_suppressElabErrors_1320_);
lean_inc(v_stx_1298_);
v___x_1324_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v___x_1323_, v_a_1304_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref_known(v___x_1323_, 14);
lean_dec(v_stx_1298_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_fst_1329_; lean_object* v___x_1331_; 
v_fst_1329_ = lean_ctor_get(v_a_1325_, 0);
lean_inc(v_fst_1329_);
lean_dec(v_a_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_fst_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_fst_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1349_; 
v_a_1334_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1336_ = v___x_1324_;
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1324_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1334_);
if (v_isShared_1337_ == 0)
{
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1334_);
v___x_1340_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
uint8_t v___y_1342_; uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_Exception_isInterrupt(v_a_1334_);
if (v___x_1346_ == 0)
{
uint8_t v___x_1347_; 
lean_inc(v_a_1334_);
v___x_1347_ = l_Lean_Exception_isRuntime(v_a_1334_);
v___y_1342_ = v___x_1347_;
goto v___jp_1341_;
}
else
{
v___y_1342_ = v___x_1346_;
goto v___jp_1341_;
}
v___jp_1341_:
{
if (v___y_1342_ == 0)
{
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_dec_ref_known(v_a_1334_, 2);
lean_dec_ref_known(v___x_1323_, 14);
lean_dec(v_stx_1298_);
return v___x_1340_;
}
else
{
lean_object* v_id_1343_; uint8_t v___x_1344_; 
v_id_1343_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_id_1343_);
lean_dec_ref_known(v_a_1334_, 2);
v___x_1344_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1338_, v_id_1343_);
lean_dec(v_id_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref_known(v___x_1323_, 14);
lean_dec(v_stx_1298_);
return v___x_1340_;
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v___x_1340_);
v___x_1345_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v___x_1323_, v_a_1304_);
lean_dec_ref_known(v___x_1323_, 14);
return v___x_1345_;
}
}
}
else
{
lean_dec(v_a_1334_);
lean_dec_ref_known(v___x_1323_, 14);
lean_dec(v_stx_1298_);
return v___x_1340_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode___closed__1);
v___x_1360_ = l_Lean_MessageData_ofExpr(v___x_1359_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1362_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1361_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1365_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_ty_x3f_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_fileName_1381_; lean_object* v_fileMap_1382_; lean_object* v_options_1383_; lean_object* v_currRecDepth_1384_; lean_object* v_maxRecDepth_1385_; lean_object* v_ref_1386_; lean_object* v_currNamespace_1387_; lean_object* v_openDecls_1388_; lean_object* v_initHeartbeats_1389_; lean_object* v_maxHeartbeats_1390_; lean_object* v_quotContext_1391_; lean_object* v_currMacroScope_1392_; uint8_t v_diag_1393_; lean_object* v_cancelTk_x3f_1394_; uint8_t v_suppressElabErrors_1395_; lean_object* v_inheritedTraceOptions_1396_; uint8_t v___x_1397_; lean_object* v_ref_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_ty_x3f_1375_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode___closed__1);
v___x_1376_ = 1;
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_box(v___x_1376_);
v___x_1379_ = lean_box(v___x_1376_);
lean_inc(v_stx_1367_);
v___x_1380_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1380_, 0, v_stx_1367_);
lean_closure_set(v___x_1380_, 1, v_ty_x3f_1375_);
lean_closure_set(v___x_1380_, 2, v___x_1378_);
lean_closure_set(v___x_1380_, 3, v___x_1379_);
lean_closure_set(v___x_1380_, 4, v___x_1377_);
v_fileName_1381_ = lean_ctor_get(v_a_1372_, 0);
v_fileMap_1382_ = lean_ctor_get(v_a_1372_, 1);
v_options_1383_ = lean_ctor_get(v_a_1372_, 2);
v_currRecDepth_1384_ = lean_ctor_get(v_a_1372_, 3);
v_maxRecDepth_1385_ = lean_ctor_get(v_a_1372_, 4);
v_ref_1386_ = lean_ctor_get(v_a_1372_, 5);
v_currNamespace_1387_ = lean_ctor_get(v_a_1372_, 6);
v_openDecls_1388_ = lean_ctor_get(v_a_1372_, 7);
v_initHeartbeats_1389_ = lean_ctor_get(v_a_1372_, 8);
v_maxHeartbeats_1390_ = lean_ctor_get(v_a_1372_, 9);
v_quotContext_1391_ = lean_ctor_get(v_a_1372_, 10);
v_currMacroScope_1392_ = lean_ctor_get(v_a_1372_, 11);
v_diag_1393_ = lean_ctor_get_uint8(v_a_1372_, sizeof(void*)*14);
v_cancelTk_x3f_1394_ = lean_ctor_get(v_a_1372_, 12);
v_suppressElabErrors_1395_ = lean_ctor_get_uint8(v_a_1372_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1396_ = lean_ctor_get(v_a_1372_, 13);
v___x_1397_ = 1;
v_ref_1398_ = l_Lean_replaceRef(v_stx_1367_, v_ref_1386_);
lean_dec(v_stx_1367_);
lean_inc_ref(v_inheritedTraceOptions_1396_);
lean_inc(v_cancelTk_x3f_1394_);
lean_inc(v_currMacroScope_1392_);
lean_inc(v_quotContext_1391_);
lean_inc(v_maxHeartbeats_1390_);
lean_inc(v_initHeartbeats_1389_);
lean_inc(v_openDecls_1388_);
lean_inc(v_currNamespace_1387_);
lean_inc(v_maxRecDepth_1385_);
lean_inc(v_currRecDepth_1384_);
lean_inc_ref(v_options_1383_);
lean_inc_ref(v_fileMap_1382_);
lean_inc_ref(v_fileName_1381_);
v___x_1399_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1399_, 0, v_fileName_1381_);
lean_ctor_set(v___x_1399_, 1, v_fileMap_1382_);
lean_ctor_set(v___x_1399_, 2, v_options_1383_);
lean_ctor_set(v___x_1399_, 3, v_currRecDepth_1384_);
lean_ctor_set(v___x_1399_, 4, v_maxRecDepth_1385_);
lean_ctor_set(v___x_1399_, 5, v_ref_1398_);
lean_ctor_set(v___x_1399_, 6, v_currNamespace_1387_);
lean_ctor_set(v___x_1399_, 7, v_openDecls_1388_);
lean_ctor_set(v___x_1399_, 8, v_initHeartbeats_1389_);
lean_ctor_set(v___x_1399_, 9, v_maxHeartbeats_1390_);
lean_ctor_set(v___x_1399_, 10, v_quotContext_1391_);
lean_ctor_set(v___x_1399_, 11, v_currMacroScope_1392_);
lean_ctor_set(v___x_1399_, 12, v_cancelTk_x3f_1394_);
lean_ctor_set(v___x_1399_, 13, v_inheritedTraceOptions_1396_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*14, v_diag_1393_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*14 + 1, v_suppressElabErrors_1395_);
v___x_1400_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1380_, v___x_1397_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v___x_1399_, v_a_1373_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; uint8_t v___y_1414_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; uint8_t v___x_1498_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1401_, v_a_1371_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___x_1402_);
v___x_1498_ = l_Lean_Expr_hasSorry(v_a_1403_);
if (v___x_1498_ == 0)
{
v___y_1443_ = v_a_1368_;
v___y_1444_ = v_a_1369_;
v___y_1445_ = v_a_1370_;
v___y_1446_ = v_a_1371_;
v___y_1447_ = v___x_1399_;
v___y_1448_ = v_a_1373_;
goto v___jp_1442_;
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Expr_hasSyntheticSorry(v_a_1403_);
if (v___x_1499_ == 0)
{
v___y_1480_ = v_a_1368_;
v___y_1481_ = v_a_1369_;
v___y_1482_ = v_a_1370_;
v___y_1483_ = v_a_1371_;
v___y_1484_ = v___x_1399_;
v___y_1485_ = v_a_1373_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1500_; lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1403_);
lean_dec_ref_known(v___x_1399_, 14);
v___x_1500_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
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
v___jp_1404_:
{
if (v___y_1414_ == 0)
{
if (lean_obj_tag(v___y_1406_) == 0)
{
lean_dec_ref_known(v___y_1406_, 2);
lean_dec_ref(v___y_1409_);
lean_dec(v_a_1403_);
return v___y_1408_;
}
else
{
lean_object* v_id_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1428_; 
v_id_1415_ = lean_ctor_get(v___y_1406_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___y_1406_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v___y_1406_, 1);
lean_dec(v_unused_1429_);
v___x_1417_ = v___y_1406_;
v_isShared_1418_ = v_isSharedCheck_1428_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_id_1415_);
lean_dec(v___y_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1428_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1412_, v_id_1415_);
lean_dec(v_id_1415_);
if (v___x_1419_ == 0)
{
lean_del_object(v___x_1417_);
lean_dec_ref(v___y_1409_);
lean_dec(v_a_1403_);
return v___y_1408_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec_ref(v___y_1408_);
v___x_1420_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1421_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1422_ = l_Lean_indentExpr(v_a_1403_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 7);
lean_ctor_set(v___x_1417_, 1, v___x_1422_);
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1420_);
v___x_1426_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1425_, v___y_1405_, v___y_1411_, v___y_1413_, v___y_1410_, v___y_1409_, v___y_1407_);
lean_dec_ref(v___y_1409_);
return v___x_1426_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1409_);
lean_dec_ref(v___y_1406_);
lean_dec(v_a_1403_);
return v___y_1408_;
}
}
v___jp_1430_:
{
lean_object* v___x_1437_; 
lean_inc(v_a_1403_);
v___x_1437_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode_evalExpr(v_a_1403_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref(v___y_1435_);
lean_dec(v_a_1403_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
v___x_1439_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1440_ = l_Lean_Exception_isInterrupt(v_a_1438_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
lean_inc(v_a_1438_);
v___x_1441_ = l_Lean_Exception_isRuntime(v_a_1438_);
v___y_1405_ = v___y_1431_;
v___y_1406_ = v_a_1438_;
v___y_1407_ = v___y_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___y_1434_;
v___y_1411_ = v___y_1432_;
v___y_1412_ = v___x_1439_;
v___y_1413_ = v___y_1433_;
v___y_1414_ = v___x_1441_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___y_1431_;
v___y_1406_ = v_a_1438_;
v___y_1407_ = v___y_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___y_1434_;
v___y_1411_ = v___y_1432_;
v___y_1412_ = v___x_1439_;
v___y_1413_ = v___y_1433_;
v___y_1414_ = v___x_1440_;
goto v___jp_1404_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1449_; 
lean_inc(v_a_1403_);
v___x_1449_ = l_Lean_Meta_getMVars(v_a_1403_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1450_, v___x_1377_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v_a_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; uint8_t v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = lean_unbox(v_a_1452_);
lean_dec(v_a_1452_);
if (v___x_1453_ == 0)
{
v___y_1431_ = v___y_1443_;
v___y_1432_ = v___y_1444_;
v___y_1433_ = v___y_1445_;
v___y_1434_ = v___y_1446_;
v___y_1435_ = v___y_1447_;
v___y_1436_ = v___y_1448_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v___y_1447_);
lean_dec(v_a_1403_);
v___x_1454_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___y_1447_);
lean_dec(v_a_1403_);
v_a_1463_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1451_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1451_);
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
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___y_1447_);
lean_dec(v_a_1403_);
v_a_1471_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1449_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1449_);
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
v___jp_1479_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v___x_1486_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1487_ = l_Lean_indentExpr(v_a_1403_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1488_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec_ref(v___y_1484_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref_known(v___x_1399_, 14);
v_a_1509_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1400_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1400_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_fileName_1534_; lean_object* v_fileMap_1535_; lean_object* v_options_1536_; lean_object* v_currRecDepth_1537_; lean_object* v_maxRecDepth_1538_; lean_object* v_ref_1539_; lean_object* v_currNamespace_1540_; lean_object* v_openDecls_1541_; lean_object* v_initHeartbeats_1542_; lean_object* v_maxHeartbeats_1543_; lean_object* v_quotContext_1544_; lean_object* v_currMacroScope_1545_; uint8_t v_diag_1546_; lean_object* v_cancelTk_x3f_1547_; uint8_t v_suppressElabErrors_1548_; lean_object* v_inheritedTraceOptions_1549_; lean_object* v_ref_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_fileName_1534_ = lean_ctor_get(v_a_1531_, 0);
v_fileMap_1535_ = lean_ctor_get(v_a_1531_, 1);
v_options_1536_ = lean_ctor_get(v_a_1531_, 2);
v_currRecDepth_1537_ = lean_ctor_get(v_a_1531_, 3);
v_maxRecDepth_1538_ = lean_ctor_get(v_a_1531_, 4);
v_ref_1539_ = lean_ctor_get(v_a_1531_, 5);
v_currNamespace_1540_ = lean_ctor_get(v_a_1531_, 6);
v_openDecls_1541_ = lean_ctor_get(v_a_1531_, 7);
v_initHeartbeats_1542_ = lean_ctor_get(v_a_1531_, 8);
v_maxHeartbeats_1543_ = lean_ctor_get(v_a_1531_, 9);
v_quotContext_1544_ = lean_ctor_get(v_a_1531_, 10);
v_currMacroScope_1545_ = lean_ctor_get(v_a_1531_, 11);
v_diag_1546_ = lean_ctor_get_uint8(v_a_1531_, sizeof(void*)*14);
v_cancelTk_x3f_1547_ = lean_ctor_get(v_a_1531_, 12);
v_suppressElabErrors_1548_ = lean_ctor_get_uint8(v_a_1531_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1549_ = lean_ctor_get(v_a_1531_, 13);
v_ref_1550_ = l_Lean_replaceRef(v_stx_1526_, v_ref_1539_);
lean_inc_ref(v_inheritedTraceOptions_1549_);
lean_inc(v_cancelTk_x3f_1547_);
lean_inc(v_currMacroScope_1545_);
lean_inc(v_quotContext_1544_);
lean_inc(v_maxHeartbeats_1543_);
lean_inc(v_initHeartbeats_1542_);
lean_inc(v_openDecls_1541_);
lean_inc(v_currNamespace_1540_);
lean_inc(v_maxRecDepth_1538_);
lean_inc(v_currRecDepth_1537_);
lean_inc_ref(v_options_1536_);
lean_inc_ref(v_fileMap_1535_);
lean_inc_ref(v_fileName_1534_);
v___x_1551_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1551_, 0, v_fileName_1534_);
lean_ctor_set(v___x_1551_, 1, v_fileMap_1535_);
lean_ctor_set(v___x_1551_, 2, v_options_1536_);
lean_ctor_set(v___x_1551_, 3, v_currRecDepth_1537_);
lean_ctor_set(v___x_1551_, 4, v_maxRecDepth_1538_);
lean_ctor_set(v___x_1551_, 5, v_ref_1550_);
lean_ctor_set(v___x_1551_, 6, v_currNamespace_1540_);
lean_ctor_set(v___x_1551_, 7, v_openDecls_1541_);
lean_ctor_set(v___x_1551_, 8, v_initHeartbeats_1542_);
lean_ctor_set(v___x_1551_, 9, v_maxHeartbeats_1543_);
lean_ctor_set(v___x_1551_, 10, v_quotContext_1544_);
lean_ctor_set(v___x_1551_, 11, v_currMacroScope_1545_);
lean_ctor_set(v___x_1551_, 12, v_cancelTk_x3f_1547_);
lean_ctor_set(v___x_1551_, 13, v_inheritedTraceOptions_1549_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*14, v_diag_1546_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*14 + 1, v_suppressElabErrors_1548_);
lean_inc(v_stx_1526_);
v___x_1552_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode_evalTerm(v_stx_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v___x_1551_, v_a_1532_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref_known(v___x_1551_, 14);
lean_dec(v_stx_1526_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_fst_1557_; lean_object* v___x_1559_; 
v_fst_1557_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_fst_1557_);
lean_dec(v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_fst_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_fst_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1577_; 
v_a_1562_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1564_ = v___x_1552_;
v_isShared_1565_ = v_isSharedCheck_1577_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1552_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1577_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1562_);
if (v_isShared_1565_ == 0)
{
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1562_);
v___x_1568_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
uint8_t v___y_1570_; uint8_t v___x_1574_; 
v___x_1574_ = l_Lean_Exception_isInterrupt(v_a_1562_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; 
lean_inc(v_a_1562_);
v___x_1575_ = l_Lean_Exception_isRuntime(v_a_1562_);
v___y_1570_ = v___x_1575_;
goto v___jp_1569_;
}
else
{
v___y_1570_ = v___x_1574_;
goto v___jp_1569_;
}
v___jp_1569_:
{
if (v___y_1570_ == 0)
{
if (lean_obj_tag(v_a_1562_) == 0)
{
lean_dec_ref_known(v_a_1562_, 2);
lean_dec_ref_known(v___x_1551_, 14);
lean_dec(v_stx_1526_);
return v___x_1568_;
}
else
{
lean_object* v_id_1571_; uint8_t v___x_1572_; 
v_id_1571_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_id_1571_);
lean_dec_ref_known(v_a_1562_, 2);
v___x_1572_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1566_, v_id_1571_);
lean_dec(v_id_1571_);
if (v___x_1572_ == 0)
{
lean_dec_ref_known(v___x_1551_, 14);
lean_dec(v_stx_1526_);
return v___x_1568_;
}
else
{
lean_object* v___x_1573_; 
lean_dec_ref(v___x_1568_);
v___x_1573_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v___x_1551_, v_a_1532_);
lean_dec_ref_known(v___x_1551_, 14);
return v___x_1573_;
}
}
}
else
{
lean_dec(v_a_1562_);
lean_dec_ref_known(v___x_1551_, 14);
lean_dec(v_stx_1526_);
return v___x_1568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1707_, lean_object* v_item_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_item_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1727_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1708_, v___x_1726_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1727_) == 0)
{
uint8_t v___x_1728_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1728_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1708_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1729_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1708_);
lean_inc_ref(v_item_1708_);
v___x_1730_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1708_);
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1732_ = lean_string_dec_lt(v___x_1729_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1734_ = lean_string_dec_lt(v___x_1729_, v___x_1733_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_string_dec_eq(v___x_1729_, v___x_1733_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1737_ = lean_string_dec_eq(v___x_1729_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1739_ = lean_string_dec_eq(v___x_1729_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1741_ = lean_string_dec_eq(v___x_1729_, v___x_1740_);
lean_dec_ref(v___x_1729_);
if (v___x_1741_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1743_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_1742_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1743_) == 0)
{
uint8_t v___x_1744_; 
lean_dec_ref_known(v___x_1743_, 1);
v___x_1744_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_1744_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1745_; 
lean_dec_ref(v___x_1730_);
v___x_1745_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1773_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_timeout_1750_; uint8_t v_binaryProofs_1751_; uint8_t v_acNf_1752_; uint8_t v_andFlattening_1753_; uint8_t v_embeddedConstraintSubst_1754_; uint8_t v_structures_1755_; uint8_t v_fixedInt_1756_; uint8_t v_enums_1757_; uint8_t v_graphviz_1758_; lean_object* v_maxSteps_1759_; uint8_t v_shortCircuit_1760_; uint8_t v_solverMode_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1772_; 
v_timeout_1750_ = lean_ctor_get(v_config_1707_, 0);
v_binaryProofs_1751_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_1752_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_1753_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1754_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_1755_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_1756_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_1757_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_1758_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_1759_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_1760_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_1761_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1763_ = v_config_1707_;
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_maxSteps_1759_);
lean_inc(v_timeout_1750_);
lean_dec(v_config_1707_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_timeout_1750_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_maxSteps_1759_);
v___x_1766_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
uint8_t v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_unbox(v_a_1746_);
lean_dec(v_a_1746_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2, v___x_1767_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 1, v_binaryProofs_1751_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 2, v_acNf_1752_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 3, v_andFlattening_1753_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1754_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 5, v_structures_1755_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 6, v_fixedInt_1756_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 7, v_enums_1757_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 8, v_graphviz_1758_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 9, v_shortCircuit_1760_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 10, v_solverMode_1761_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1766_);
v___x_1769_ = v___x_1748_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1766_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v_config_1707_);
v_a_1774_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1745_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1745_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1782_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1743_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1743_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec_ref(v___x_1729_);
v___x_1790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1791_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_1790_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1791_) == 0)
{
uint8_t v___x_1792_; 
lean_dec_ref_known(v___x_1791_, 1);
v___x_1792_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1793_; 
lean_dec_ref(v___x_1730_);
lean_inc_ref(v_item_1708_);
v___x_1793_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_value_1794_; lean_object* v___x_1795_; 
lean_dec_ref_known(v___x_1793_, 1);
v_value_1794_ = lean_ctor_get(v_item_1708_, 2);
lean_inc(v_value_1794_);
lean_dec_ref(v_item_1708_);
v___x_1795_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1794_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1823_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1823_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1823_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
uint8_t v_trimProofs_1800_; uint8_t v_binaryProofs_1801_; uint8_t v_acNf_1802_; uint8_t v_andFlattening_1803_; uint8_t v_embeddedConstraintSubst_1804_; uint8_t v_structures_1805_; uint8_t v_fixedInt_1806_; uint8_t v_enums_1807_; uint8_t v_graphviz_1808_; lean_object* v_maxSteps_1809_; uint8_t v_shortCircuit_1810_; uint8_t v_solverMode_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
v_trimProofs_1800_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_1801_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_1802_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_1803_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1804_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_1805_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_1806_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_1807_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_1808_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_1809_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_1810_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_1811_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v_config_1707_, 0);
lean_dec(v_unused_1822_);
v___x_1813_ = v_config_1707_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_maxSteps_1809_);
lean_dec(v_config_1707_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_a_1796_);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1796_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_maxSteps_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2, v_trimProofs_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 1, v_binaryProofs_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 2, v_acNf_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 3, v_andFlattening_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 5, v_structures_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 6, v_fixedInt_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 7, v_enums_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 8, v_graphviz_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 9, v_shortCircuit_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*2 + 10, v_solverMode_1811_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1816_);
v___x_1818_ = v___x_1798_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_config_1707_);
v_a_1824_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1795_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1795_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1832_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1793_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1793_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
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
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1840_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1791_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1791_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref(v___x_1729_);
v___x_1848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1849_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_1848_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1849_) == 0)
{
uint8_t v___x_1850_; 
lean_dec_ref_known(v___x_1849_, 1);
v___x_1850_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_1850_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1851_; 
lean_dec_ref(v___x_1730_);
v___x_1851_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1879_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1879_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1879_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_timeout_1856_; uint8_t v_trimProofs_1857_; uint8_t v_binaryProofs_1858_; uint8_t v_acNf_1859_; uint8_t v_andFlattening_1860_; uint8_t v_embeddedConstraintSubst_1861_; uint8_t v_fixedInt_1862_; uint8_t v_enums_1863_; uint8_t v_graphviz_1864_; lean_object* v_maxSteps_1865_; uint8_t v_shortCircuit_1866_; uint8_t v_solverMode_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1878_; 
v_timeout_1856_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_1857_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_1858_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_1859_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_1860_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1861_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_fixedInt_1862_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_1863_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_1864_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_1865_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_1866_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_1867_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1869_ = v_config_1707_;
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_maxSteps_1865_);
lean_inc(v_timeout_1856_);
lean_dec(v_config_1707_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_timeout_1856_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_maxSteps_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*2, v_trimProofs_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*2 + 1, v_binaryProofs_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*2 + 2, v_acNf_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*2 + 3, v_andFlattening_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1861_);
v___x_1872_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
uint8_t v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 5, v___x_1873_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 6, v_fixedInt_1862_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 7, v_enums_1863_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 8, v_graphviz_1864_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 9, v_shortCircuit_1866_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 10, v_solverMode_1867_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1872_);
v___x_1875_ = v___x_1854_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1872_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_config_1707_);
v_a_1880_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1851_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1851_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1888_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1849_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1849_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v___x_1729_);
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1897_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_1896_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1897_) == 0)
{
uint8_t v___x_1898_; 
lean_dec_ref_known(v___x_1897_, 1);
v___x_1898_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1899_; 
lean_dec_ref(v___x_1730_);
lean_inc_ref(v_item_1708_);
v___x_1899_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_value_1900_; lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1899_, 1);
v_value_1900_ = lean_ctor_get(v_item_1708_, 2);
lean_inc(v_value_1900_);
lean_dec_ref(v_item_1708_);
v___x_1901_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1900_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1929_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1929_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1929_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_timeout_1906_; uint8_t v_trimProofs_1907_; uint8_t v_binaryProofs_1908_; uint8_t v_acNf_1909_; uint8_t v_andFlattening_1910_; uint8_t v_embeddedConstraintSubst_1911_; uint8_t v_structures_1912_; uint8_t v_fixedInt_1913_; uint8_t v_enums_1914_; uint8_t v_graphviz_1915_; lean_object* v_maxSteps_1916_; uint8_t v_shortCircuit_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1928_; 
v_timeout_1906_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_1907_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_1908_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_1909_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_1910_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1911_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_1912_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_1913_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_1914_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_1915_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_1916_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_1917_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1919_ = v_config_1707_;
v_isShared_1920_ = v_isSharedCheck_1928_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_maxSteps_1916_);
lean_inc(v_timeout_1906_);
lean_dec(v_config_1707_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1928_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_timeout_1906_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_maxSteps_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2, v_trimProofs_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 1, v_binaryProofs_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 2, v_acNf_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 3, v_andFlattening_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 5, v_structures_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 6, v_fixedInt_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 7, v_enums_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 8, v_graphviz_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*2 + 9, v_shortCircuit_1917_);
v___x_1922_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
uint8_t v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_unbox(v_a_1902_);
lean_dec(v_a_1902_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*2 + 10, v___x_1923_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1922_);
v___x_1925_ = v___x_1904_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1922_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_config_1707_);
v_a_1930_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1901_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1901_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1938_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1899_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1899_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1946_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1897_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1897_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_string_dec_eq(v___x_1729_, v___x_1731_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1956_ = lean_string_dec_eq(v___x_1729_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1958_ = lean_string_dec_eq(v___x_1729_, v___x_1957_);
lean_dec_ref(v___x_1729_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1960_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_1959_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1960_) == 0)
{
uint8_t v___x_1961_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1961_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_1961_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1962_; 
lean_dec_ref(v___x_1730_);
v___x_1962_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1990_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1990_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1990_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_timeout_1967_; uint8_t v_trimProofs_1968_; uint8_t v_binaryProofs_1969_; uint8_t v_acNf_1970_; uint8_t v_andFlattening_1971_; uint8_t v_embeddedConstraintSubst_1972_; uint8_t v_structures_1973_; uint8_t v_fixedInt_1974_; uint8_t v_enums_1975_; uint8_t v_graphviz_1976_; lean_object* v_maxSteps_1977_; uint8_t v_solverMode_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1989_; 
v_timeout_1967_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_1968_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_1969_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_1970_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_1971_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1972_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_1973_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_1974_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_1975_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_1976_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_1977_ = lean_ctor_get(v_config_1707_, 1);
v_solverMode_1978_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1980_ = v_config_1707_;
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_maxSteps_1977_);
lean_inc(v_timeout_1967_);
lean_dec(v_config_1707_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_timeout_1967_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_maxSteps_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2, v_trimProofs_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 1, v_binaryProofs_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 2, v_acNf_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 3, v_andFlattening_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 5, v_structures_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 6, v_fixedInt_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 7, v_enums_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*2 + 8, v_graphviz_1976_);
v___x_1983_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
uint8_t v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 9, v___x_1984_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 10, v_solverMode_1978_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1983_);
v___x_1986_ = v___x_1965_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1983_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v_config_1707_);
v_a_1991_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1962_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1962_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_1999_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1960_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1960_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref(v___x_1729_);
v___x_2007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_2008_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2007_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2008_) == 0)
{
uint8_t v___x_2009_; 
lean_dec_ref_known(v___x_2008_, 1);
v___x_2009_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2010_; 
lean_dec_ref(v___x_1730_);
lean_inc_ref(v_item_1708_);
v___x_2010_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_value_2011_; lean_object* v___x_2012_; 
lean_dec_ref_known(v___x_2010_, 1);
v_value_2011_ = lean_ctor_get(v_item_1708_, 2);
lean_inc(v_value_2011_);
lean_dec_ref(v_item_1708_);
v___x_2012_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2011_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2040_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2040_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2040_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_timeout_2017_; uint8_t v_trimProofs_2018_; uint8_t v_binaryProofs_2019_; uint8_t v_acNf_2020_; uint8_t v_andFlattening_2021_; uint8_t v_embeddedConstraintSubst_2022_; uint8_t v_structures_2023_; uint8_t v_fixedInt_2024_; uint8_t v_enums_2025_; uint8_t v_graphviz_2026_; uint8_t v_shortCircuit_2027_; uint8_t v_solverMode_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_timeout_2017_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2018_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2019_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2020_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2021_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2022_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2023_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2024_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2025_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2026_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_shortCircuit_2027_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2028_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_config_1707_, 1);
lean_dec(v_unused_2039_);
v___x_2030_ = v_config_1707_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_timeout_2017_);
lean_dec(v_config_1707_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_a_2013_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_timeout_2017_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_a_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2, v_trimProofs_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 1, v_binaryProofs_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 2, v_acNf_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 3, v_andFlattening_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 5, v_structures_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 6, v_fixedInt_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 7, v_enums_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 8, v_graphviz_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 9, v_shortCircuit_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*2 + 10, v_solverMode_2028_);
v___x_2033_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2033_);
v___x_2035_ = v___x_2015_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_config_1707_);
v_a_2041_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2012_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2012_);
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
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2049_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2010_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2010_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2057_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2008_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2008_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v___x_1729_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_2066_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2065_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2066_) == 0)
{
uint8_t v___x_2067_; 
lean_dec_ref_known(v___x_2066_, 1);
v___x_2067_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_1730_);
v___x_2068_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2096_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2096_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2096_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_timeout_2073_; uint8_t v_trimProofs_2074_; uint8_t v_binaryProofs_2075_; uint8_t v_acNf_2076_; uint8_t v_andFlattening_2077_; uint8_t v_embeddedConstraintSubst_2078_; uint8_t v_structures_2079_; uint8_t v_fixedInt_2080_; uint8_t v_enums_2081_; lean_object* v_maxSteps_2082_; uint8_t v_shortCircuit_2083_; uint8_t v_solverMode_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2095_; 
v_timeout_2073_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2074_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2075_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2076_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2077_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2078_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2079_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2080_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2081_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_maxSteps_2082_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2083_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2084_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2086_ = v_config_1707_;
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_maxSteps_2082_);
lean_inc(v_timeout_2073_);
lean_dec(v_config_1707_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_timeout_2073_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_maxSteps_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2, v_trimProofs_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 1, v_binaryProofs_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 2, v_acNf_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 3, v_andFlattening_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 5, v_structures_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 6, v_fixedInt_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2094_, sizeof(void*)*2 + 7, v_enums_2081_);
v___x_2089_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
uint8_t v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_unbox(v_a_2069_);
lean_dec(v_a_2069_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2 + 8, v___x_2090_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2 + 9, v_shortCircuit_2083_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2 + 10, v_solverMode_2084_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2089_);
v___x_2092_ = v___x_2071_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2089_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_config_1707_);
v_a_2097_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2068_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2068_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2105_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2066_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2066_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
else
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2114_ = lean_string_dec_lt(v___x_1729_, v___x_2113_);
if (v___x_2114_ == 0)
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_string_dec_eq(v___x_1729_, v___x_2113_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2117_ = lean_string_dec_eq(v___x_1729_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2119_ = lean_string_dec_eq(v___x_1729_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2121_ = lean_string_dec_eq(v___x_1729_, v___x_2120_);
lean_dec_ref(v___x_1729_);
if (v___x_2121_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2123_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2122_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2123_) == 0)
{
uint8_t v___x_2124_; 
lean_dec_ref_known(v___x_2123_, 1);
v___x_2124_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2124_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2125_; 
lean_dec_ref(v___x_1730_);
v___x_2125_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2153_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2153_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2153_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_timeout_2130_; uint8_t v_trimProofs_2131_; uint8_t v_binaryProofs_2132_; uint8_t v_acNf_2133_; uint8_t v_andFlattening_2134_; uint8_t v_embeddedConstraintSubst_2135_; uint8_t v_structures_2136_; uint8_t v_enums_2137_; uint8_t v_graphviz_2138_; lean_object* v_maxSteps_2139_; uint8_t v_shortCircuit_2140_; uint8_t v_solverMode_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2152_; 
v_timeout_2130_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2131_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2132_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2133_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2134_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2135_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2136_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_enums_2137_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2138_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2139_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2140_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2141_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2143_ = v_config_1707_;
v_isShared_2144_ = v_isSharedCheck_2152_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_maxSteps_2139_);
lean_inc(v_timeout_2130_);
lean_dec(v_config_1707_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2152_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_timeout_2130_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_maxSteps_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2, v_trimProofs_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 1, v_binaryProofs_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 2, v_acNf_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 3, v_andFlattening_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 5, v_structures_2136_);
v___x_2146_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
uint8_t v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_unbox(v_a_2126_);
lean_dec(v_a_2126_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*2 + 6, v___x_2147_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*2 + 7, v_enums_2137_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*2 + 8, v_graphviz_2138_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*2 + 9, v_shortCircuit_2140_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*2 + 10, v_solverMode_2141_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2146_);
v___x_2149_ = v___x_2128_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2146_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_config_1707_);
v_a_2154_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2125_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2125_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2162_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2123_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2123_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v___x_1729_);
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2171_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2170_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2171_) == 0)
{
uint8_t v___x_2172_; 
lean_dec_ref_known(v___x_2171_, 1);
v___x_2172_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2172_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2173_; 
lean_dec_ref(v___x_1730_);
v___x_2173_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2201_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2201_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2201_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_timeout_2178_; uint8_t v_trimProofs_2179_; uint8_t v_binaryProofs_2180_; uint8_t v_acNf_2181_; uint8_t v_andFlattening_2182_; uint8_t v_embeddedConstraintSubst_2183_; uint8_t v_structures_2184_; uint8_t v_fixedInt_2185_; uint8_t v_graphviz_2186_; lean_object* v_maxSteps_2187_; uint8_t v_shortCircuit_2188_; uint8_t v_solverMode_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2200_; 
v_timeout_2178_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2179_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2180_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2181_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2182_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2183_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2184_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2185_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_graphviz_2186_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2187_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2188_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2189_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2191_ = v_config_1707_;
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_maxSteps_2187_);
lean_inc(v_timeout_2178_);
lean_dec(v_config_1707_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_timeout_2178_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_maxSteps_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2, v_trimProofs_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 1, v_binaryProofs_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 2, v_acNf_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 3, v_andFlattening_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 5, v_structures_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2 + 6, v_fixedInt_2185_);
v___x_2194_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
uint8_t v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_unbox(v_a_2174_);
lean_dec(v_a_2174_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2 + 7, v___x_2195_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2 + 8, v_graphviz_2186_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2 + 9, v_shortCircuit_2188_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2 + 10, v_solverMode_2189_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2194_);
v___x_2197_ = v___x_2176_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2194_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_config_1707_);
v_a_2202_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2173_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2173_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2210_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2171_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2171_);
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
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v___x_1729_);
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2219_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2218_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2219_) == 0)
{
uint8_t v___x_2220_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2220_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2221_; 
lean_dec_ref(v___x_1730_);
v___x_2221_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2249_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2249_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2249_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_timeout_2226_; uint8_t v_trimProofs_2227_; uint8_t v_binaryProofs_2228_; uint8_t v_acNf_2229_; uint8_t v_andFlattening_2230_; uint8_t v_structures_2231_; uint8_t v_fixedInt_2232_; uint8_t v_enums_2233_; uint8_t v_graphviz_2234_; lean_object* v_maxSteps_2235_; uint8_t v_shortCircuit_2236_; uint8_t v_solverMode_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2248_; 
v_timeout_2226_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2227_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2228_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2229_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2230_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_structures_2231_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2232_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2233_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2234_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2235_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2236_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2237_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2239_ = v_config_1707_;
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_maxSteps_2235_);
lean_inc(v_timeout_2226_);
lean_dec(v_config_1707_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_timeout_2226_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_maxSteps_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2247_, sizeof(void*)*2, v_trimProofs_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2247_, sizeof(void*)*2 + 1, v_binaryProofs_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2247_, sizeof(void*)*2 + 2, v_acNf_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2247_, sizeof(void*)*2 + 3, v_andFlattening_2230_);
v___x_2242_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
uint8_t v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 4, v___x_2243_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 5, v_structures_2231_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 6, v_fixedInt_2232_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 7, v_enums_2233_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 8, v_graphviz_2234_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 9, v_shortCircuit_2236_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 10, v_solverMode_2237_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2242_);
v___x_2245_ = v___x_2224_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2242_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_config_1707_);
v_a_2250_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2221_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2221_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2258_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2219_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2219_);
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
else
{
uint8_t v___x_2266_; 
lean_dec_ref(v___x_1729_);
lean_dec_ref(v_config_1707_);
v___x_2266_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2266_ == 0)
{
lean_dec_ref(v_item_1708_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v_value_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v___x_1730_);
v_value_2267_ = lean_ctor_get(v_item_1708_, 2);
lean_inc(v_value_2267_);
lean_dec_ref(v_item_1708_);
v___x_2268_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2267_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_2268_;
}
}
}
else
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2270_ = lean_string_dec_eq(v___x_1729_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2272_ = lean_string_dec_eq(v___x_1729_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2274_ = lean_string_dec_eq(v___x_1729_, v___x_2273_);
lean_dec_ref(v___x_1729_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2276_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2275_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2276_) == 0)
{
uint8_t v___x_2277_; 
lean_dec_ref_known(v___x_2276_, 1);
v___x_2277_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2278_; 
lean_dec_ref(v___x_1730_);
v___x_2278_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2306_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2306_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2306_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_timeout_2283_; uint8_t v_trimProofs_2284_; uint8_t v_acNf_2285_; uint8_t v_andFlattening_2286_; uint8_t v_embeddedConstraintSubst_2287_; uint8_t v_structures_2288_; uint8_t v_fixedInt_2289_; uint8_t v_enums_2290_; uint8_t v_graphviz_2291_; lean_object* v_maxSteps_2292_; uint8_t v_shortCircuit_2293_; uint8_t v_solverMode_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2305_; 
v_timeout_2283_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2284_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_acNf_2285_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_andFlattening_2286_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2287_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2288_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2289_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2290_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2291_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2292_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2293_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2294_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2296_ = v_config_1707_;
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_maxSteps_2292_);
lean_inc(v_timeout_2283_);
lean_dec(v_config_1707_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_timeout_2283_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_maxSteps_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2304_, sizeof(void*)*2, v_trimProofs_2284_);
v___x_2299_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
uint8_t v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_unbox(v_a_2279_);
lean_dec(v_a_2279_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 1, v___x_2300_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 2, v_acNf_2285_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 3, v_andFlattening_2286_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2287_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 5, v_structures_2288_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 6, v_fixedInt_2289_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 7, v_enums_2290_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 8, v_graphviz_2291_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 9, v_shortCircuit_2293_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*2 + 10, v_solverMode_2294_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2299_);
v___x_2302_ = v___x_2281_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2299_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_config_1707_);
v_a_2307_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2278_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2278_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2315_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2276_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2276_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v___x_1729_);
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2324_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2323_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2324_) == 0)
{
uint8_t v___x_2325_; 
lean_dec_ref_known(v___x_2324_, 1);
v___x_2325_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2325_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2326_; 
lean_dec_ref(v___x_1730_);
v___x_2326_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2354_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2354_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2354_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_timeout_2331_; uint8_t v_trimProofs_2332_; uint8_t v_binaryProofs_2333_; uint8_t v_acNf_2334_; uint8_t v_embeddedConstraintSubst_2335_; uint8_t v_structures_2336_; uint8_t v_fixedInt_2337_; uint8_t v_enums_2338_; uint8_t v_graphviz_2339_; lean_object* v_maxSteps_2340_; uint8_t v_shortCircuit_2341_; uint8_t v_solverMode_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2353_; 
v_timeout_2331_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2332_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2333_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_acNf_2334_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 2);
v_embeddedConstraintSubst_2335_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2336_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2337_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2338_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2339_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2340_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2341_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2342_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2344_ = v_config_1707_;
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_maxSteps_2340_);
lean_inc(v_timeout_2331_);
lean_dec(v_config_1707_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_timeout_2331_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_maxSteps_2340_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, sizeof(void*)*2, v_trimProofs_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, sizeof(void*)*2 + 1, v_binaryProofs_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, sizeof(void*)*2 + 2, v_acNf_2334_);
v___x_2347_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
uint8_t v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_unbox(v_a_2327_);
lean_dec(v_a_2327_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 3, v___x_2348_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2335_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 5, v_structures_2336_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 6, v_fixedInt_2337_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 7, v_enums_2338_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 8, v_graphviz_2339_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 9, v_shortCircuit_2341_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 10, v_solverMode_2342_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2347_);
v___x_2350_ = v___x_2329_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2347_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_config_1707_);
v_a_2355_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2326_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2326_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2363_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2324_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2324_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v___x_1729_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2372_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1708_, v___x_2371_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2372_) == 0)
{
uint8_t v___x_2373_; 
lean_dec_ref_known(v___x_2372_, 1);
v___x_2373_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1730_);
if (v___x_2373_ == 0)
{
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_item_1717_ = v___x_1730_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_2374_; 
lean_dec_ref(v___x_1730_);
v___x_2374_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2402_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2402_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2402_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_timeout_2379_; uint8_t v_trimProofs_2380_; uint8_t v_binaryProofs_2381_; uint8_t v_andFlattening_2382_; uint8_t v_embeddedConstraintSubst_2383_; uint8_t v_structures_2384_; uint8_t v_fixedInt_2385_; uint8_t v_enums_2386_; uint8_t v_graphviz_2387_; lean_object* v_maxSteps_2388_; uint8_t v_shortCircuit_2389_; uint8_t v_solverMode_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2401_; 
v_timeout_2379_ = lean_ctor_get(v_config_1707_, 0);
v_trimProofs_2380_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2);
v_binaryProofs_2381_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 1);
v_andFlattening_2382_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2383_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 4);
v_structures_2384_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 5);
v_fixedInt_2385_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 6);
v_enums_2386_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 7);
v_graphviz_2387_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 8);
v_maxSteps_2388_ = lean_ctor_get(v_config_1707_, 1);
v_shortCircuit_2389_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 9);
v_solverMode_2390_ = lean_ctor_get_uint8(v_config_1707_, sizeof(void*)*2 + 10);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_config_1707_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2392_ = v_config_1707_;
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_maxSteps_2388_);
lean_inc(v_timeout_2379_);
lean_dec(v_config_1707_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_timeout_2379_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_maxSteps_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2400_, sizeof(void*)*2, v_trimProofs_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2400_, sizeof(void*)*2 + 1, v_binaryProofs_2381_);
v___x_2395_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
uint8_t v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 2, v___x_2396_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 3, v_andFlattening_2382_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2383_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 5, v_structures_2384_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 6, v_fixedInt_2385_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 7, v_enums_2386_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 8, v_graphviz_2387_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 9, v_shortCircuit_2389_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2 + 10, v_solverMode_2390_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2395_);
v___x_2398_ = v___x_2377_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2395_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref(v_config_1707_);
v_a_2403_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2374_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2374_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2411_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2372_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2372_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_config_1707_);
v_item_1717_ = v_item_1708_;
v___y_1718_ = v___y_1709_;
v___y_1719_ = v___y_1710_;
v___y_1720_ = v___y_1711_;
v___y_1721_ = v___y_1712_;
v___y_1722_ = v___y_1713_;
v___y_1723_ = v___y_1714_;
goto v___jp_1716_;
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_item_1708_);
lean_dec_ref(v_config_1707_);
v_a_2419_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_1727_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_1727_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
v___jp_1716_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1725_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1717_, v___x_1724_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2427_, lean_object* v_item_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2427_, v_item_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2439_, v___y_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2475_, lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2485_, v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2495_, lean_object* v_macroStack_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2495_, v_macroStack_2496_, v___y_2501_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2505_, lean_object* v_macroStack_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2505_, v_macroStack_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_box(0);
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2517_ = l_Lean_mkConst(v___x_2516_, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2520_, lean_object* v_cfgItem_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2530_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2520_, v_cfgItem_2521_, v___x_2529_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2531_, lean_object* v_cfgItem_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___lam__0(v_cfg_2531_, v_cfgItem_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v_cfgItem_2532_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object* v_cfg_2542_, lean_object* v_init_2543_, uint8_t v_logExceptions_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_onErr_2549_; lean_object* v_eval_2550_; 
v_onErr_2549_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0));
v_eval_2550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2544_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2550_, v_init_2543_, v_cfg_2542_, v_onErr_2549_, v_logExceptions_2544_, v_a_2546_, v_a_2547_);
return v___x_2551_;
}
else
{
uint8_t v_recover_2552_; lean_object* v___x_2553_; 
v_recover_2552_ = lean_ctor_get_uint8(v_a_2545_, sizeof(void*)*1);
v___x_2553_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2550_, v_init_2543_, v_cfg_2542_, v_onErr_2549_, v_recover_2552_, v_a_2546_, v_a_2547_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2554_, lean_object* v_init_2555_, lean_object* v_logExceptions_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
uint8_t v_logExceptions_boxed_2561_; lean_object* v_res_2562_; 
v_logExceptions_boxed_2561_ = lean_unbox(v_logExceptions_2556_);
v_res_2562_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_cfg_2554_, v_init_2555_, v_logExceptions_boxed_2561_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object* v_cfg_2563_, lean_object* v_init_2564_, uint8_t v_logExceptions_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_cfg_2563_, v_init_2564_, v_logExceptions_2565_, v_a_2566_, v_a_2572_, v_a_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object* v_cfg_2576_, lean_object* v_init_2577_, lean_object* v_logExceptions_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
uint8_t v_logExceptions_boxed_2588_; lean_object* v_res_2589_; 
v_logExceptions_boxed_2588_ = lean_unbox(v_logExceptions_2578_);
v_res_2589_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(v_cfg_2576_, v_init_2577_, v_logExceptions_boxed_2588_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_2604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_2606_ = l_Lean_Meta_registerSimpAttr(v___x_2603_, v___x_2604_, v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_2625_ = l_Lean_Meta_registerSimpAttr(v___x_2622_, v___x_2623_, v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2____boxed(lean_object* v_a_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
return v_res_2627_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2633_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_2634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_2636_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_2637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
lean_ctor_set(v___x_2637_, 2, v___x_2635_);
lean_ctor_set(v___x_2637_, 3, v___x_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_2640_ = lean_st_mk_ref(v___x_2639_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
return v_res_2643_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_2660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_2661_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_2663_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_2659_, v___x_2660_, v___x_2661_, v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
return v_res_2665_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
lean_ctor_set(v___x_2671_, 2, v___x_2670_);
lean_ctor_set(v___x_2671_, 3, v___x_2670_);
lean_ctor_set(v___x_2671_, 4, v___x_2669_);
lean_ctor_set(v___x_2671_, 5, v___x_2669_);
lean_ctor_set(v___x_2671_, 6, v___x_2669_);
lean_ctor_set(v___x_2671_, 7, v___x_2669_);
lean_ctor_set(v___x_2671_, 8, v___x_2669_);
lean_ctor_set(v___x_2671_, 9, v___x_2669_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_unsigned_to_nat(32u);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2675_ = ((size_t)5ULL);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_unsigned_to_nat(32u);
v___x_2678_ = lean_mk_empty_array_with_capacity(v___x_2677_);
v___x_2679_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3);
v___x_2680_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
lean_ctor_set(v___x_2680_, 2, v___x_2676_);
lean_ctor_set(v___x_2680_, 3, v___x_2676_);
lean_ctor_set_usize(v___x_2680_, 4, v___x_2675_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = lean_box(1);
v___x_2682_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4);
v___x_2683_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_2684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___x_2682_);
lean_ctor_set(v___x_2684_, 2, v___x_2681_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(lean_object* v_msgData_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v_env_2690_; lean_object* v_options_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2689_ = lean_st_ref_get(v___y_2687_);
v_env_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc_ref(v_env_2690_);
lean_dec(v___x_2689_);
v_options_2691_ = lean_ctor_get(v___y_2686_, 2);
v___x_2692_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_2693_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2691_);
v___x_2694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2694_, 0, v_env_2690_);
lean_ctor_set(v___x_2694_, 1, v___x_2692_);
lean_ctor_set(v___x_2694_, 2, v___x_2693_);
lean_ctor_set(v___x_2694_, 3, v_options_2691_);
v___x_2695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v_msgData_2685_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___boxed(lean_object* v_msgData_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msgData_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_ref_2706_; lean_object* v___x_2707_; lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2716_; 
v_ref_2706_ = lean_ctor_get(v___y_2703_, 5);
v___x_2707_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msg_2702_, v___y_2703_, v___y_2704_);
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_inc(v_ref_2706_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_ref_2706_);
lean_ctor_set(v___x_2712_, 1, v_a_2708_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 1);
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg___boxed(lean_object* v_msg_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_2722_, lean_object* v_msg_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_fileName_2727_; lean_object* v_fileMap_2728_; lean_object* v_options_2729_; lean_object* v_currRecDepth_2730_; lean_object* v_maxRecDepth_2731_; lean_object* v_ref_2732_; lean_object* v_currNamespace_2733_; lean_object* v_openDecls_2734_; lean_object* v_initHeartbeats_2735_; lean_object* v_maxHeartbeats_2736_; lean_object* v_quotContext_2737_; lean_object* v_currMacroScope_2738_; uint8_t v_diag_2739_; lean_object* v_cancelTk_x3f_2740_; uint8_t v_suppressElabErrors_2741_; lean_object* v_inheritedTraceOptions_2742_; lean_object* v_ref_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_fileName_2727_ = lean_ctor_get(v___y_2724_, 0);
v_fileMap_2728_ = lean_ctor_get(v___y_2724_, 1);
v_options_2729_ = lean_ctor_get(v___y_2724_, 2);
v_currRecDepth_2730_ = lean_ctor_get(v___y_2724_, 3);
v_maxRecDepth_2731_ = lean_ctor_get(v___y_2724_, 4);
v_ref_2732_ = lean_ctor_get(v___y_2724_, 5);
v_currNamespace_2733_ = lean_ctor_get(v___y_2724_, 6);
v_openDecls_2734_ = lean_ctor_get(v___y_2724_, 7);
v_initHeartbeats_2735_ = lean_ctor_get(v___y_2724_, 8);
v_maxHeartbeats_2736_ = lean_ctor_get(v___y_2724_, 9);
v_quotContext_2737_ = lean_ctor_get(v___y_2724_, 10);
v_currMacroScope_2738_ = lean_ctor_get(v___y_2724_, 11);
v_diag_2739_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*14);
v_cancelTk_x3f_2740_ = lean_ctor_get(v___y_2724_, 12);
v_suppressElabErrors_2741_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2742_ = lean_ctor_get(v___y_2724_, 13);
v_ref_2743_ = l_Lean_replaceRef(v_ref_2722_, v_ref_2732_);
lean_inc_ref(v_inheritedTraceOptions_2742_);
lean_inc(v_cancelTk_x3f_2740_);
lean_inc(v_currMacroScope_2738_);
lean_inc(v_quotContext_2737_);
lean_inc(v_maxHeartbeats_2736_);
lean_inc(v_initHeartbeats_2735_);
lean_inc(v_openDecls_2734_);
lean_inc(v_currNamespace_2733_);
lean_inc(v_maxRecDepth_2731_);
lean_inc(v_currRecDepth_2730_);
lean_inc_ref(v_options_2729_);
lean_inc_ref(v_fileMap_2728_);
lean_inc_ref(v_fileName_2727_);
v___x_2744_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2744_, 0, v_fileName_2727_);
lean_ctor_set(v___x_2744_, 1, v_fileMap_2728_);
lean_ctor_set(v___x_2744_, 2, v_options_2729_);
lean_ctor_set(v___x_2744_, 3, v_currRecDepth_2730_);
lean_ctor_set(v___x_2744_, 4, v_maxRecDepth_2731_);
lean_ctor_set(v___x_2744_, 5, v_ref_2743_);
lean_ctor_set(v___x_2744_, 6, v_currNamespace_2733_);
lean_ctor_set(v___x_2744_, 7, v_openDecls_2734_);
lean_ctor_set(v___x_2744_, 8, v_initHeartbeats_2735_);
lean_ctor_set(v___x_2744_, 9, v_maxHeartbeats_2736_);
lean_ctor_set(v___x_2744_, 10, v_quotContext_2737_);
lean_ctor_set(v___x_2744_, 11, v_currMacroScope_2738_);
lean_ctor_set(v___x_2744_, 12, v_cancelTk_x3f_2740_);
lean_ctor_set(v___x_2744_, 13, v_inheritedTraceOptions_2742_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*14, v_diag_2739_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*14 + 1, v_suppressElabErrors_2741_);
v___x_2745_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_2723_, v___x_2744_, v___y_2725_);
lean_dec_ref_known(v___x_2744_, 14);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_2746_, lean_object* v_msg_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_2746_, v_msg_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v_ref_2746_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_2773_, lean_object* v_declHint_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; lean_object* v_env_2778_; uint8_t v___x_2779_; 
v___x_2777_ = lean_st_ref_get(v___y_2775_);
v_env_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_env_2778_);
lean_dec(v___x_2777_);
v___x_2779_ = l_Lean_Name_isAnonymous(v_declHint_2774_);
if (v___x_2779_ == 0)
{
uint8_t v_isExporting_2780_; 
v_isExporting_2780_ = lean_ctor_get_uint8(v_env_2778_, sizeof(void*)*8);
if (v_isExporting_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_dec_ref(v_env_2778_);
lean_dec(v_declHint_2774_);
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_msg_2773_);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
lean_inc_ref(v_env_2778_);
v___x_2782_ = l_Lean_Environment_setExporting(v_env_2778_, v___x_2779_);
lean_inc(v_declHint_2774_);
lean_inc_ref(v___x_2782_);
v___x_2783_ = l_Lean_Environment_contains(v___x_2782_, v_declHint_2774_, v_isExporting_2780_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v___x_2782_);
lean_dec_ref(v_env_2778_);
lean_dec(v_declHint_2774_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_msg_2773_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_c_2790_; lean_object* v___x_2791_; 
v___x_2785_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_2786_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
v___x_2787_ = l_Lean_Options_empty;
v___x_2788_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2782_);
lean_ctor_set(v___x_2788_, 1, v___x_2785_);
lean_ctor_set(v___x_2788_, 2, v___x_2786_);
lean_ctor_set(v___x_2788_, 3, v___x_2787_);
lean_inc(v_declHint_2774_);
v___x_2789_ = l_Lean_MessageData_ofConstName(v_declHint_2774_, v___x_2779_);
v_c_2790_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2790_, 0, v___x_2788_);
lean_ctor_set(v_c_2790_, 1, v___x_2789_);
v___x_2791_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2778_, v_declHint_2774_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v_env_2778_);
lean_dec(v_declHint_2774_);
v___x_2792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_c_2790_);
v___x_2794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_note(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_msg_2773_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
else
{
lean_object* v_val_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2834_; 
v_val_2799_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2801_ = v___x_2791_;
v_isShared_2802_ = v_isSharedCheck_2834_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_val_2799_);
lean_dec(v___x_2791_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2834_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_mod_2806_; uint8_t v___x_2807_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lean_Environment_header(v_env_2778_);
lean_dec_ref(v_env_2778_);
v___x_2805_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2804_);
v_mod_2806_ = lean_array_get(v___x_2803_, v___x_2805_, v_val_2799_);
lean_dec(v_val_2799_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = l_Lean_isPrivateName(v_declHint_2774_);
lean_dec(v_declHint_2774_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v_c_2790_);
v___x_2810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = l_Lean_MessageData_ofName(v_mod_2806_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_MessageData_note(v___x_2815_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v_msg_2773_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2817_);
v___x_2819_ = v___x_2801_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v_c_2790_);
v___x_2823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_MessageData_ofName(v_mod_2806_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_MessageData_note(v___x_2828_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v_msg_2773_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2830_);
v___x_2832_ = v___x_2801_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2835_; 
lean_dec_ref(v_env_2778_);
lean_dec(v_declHint_2774_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_msg_2773_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2836_, lean_object* v_declHint_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_2836_, v_declHint_2837_, v___y_2838_);
lean_dec(v___y_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_2841_, lean_object* v_declHint_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2856_; 
v___x_2846_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_2841_, v_declHint_2842_, v___y_2844_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2856_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2856_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2851_ = l_Lean_unknownIdentifierMessageTag;
v___x_2852_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v_a_2847_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2852_);
v___x_2854_ = v___x_2849_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2857_, lean_object* v_declHint_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2857_, v_declHint_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_2863_, lean_object* v_msg_2864_, lean_object* v_declHint_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v_a_2870_; lean_object* v___x_2871_; 
v___x_2869_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_2864_, v_declHint_2865_, v___y_2866_, v___y_2867_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_2863_, v_a_2870_, v___y_2866_, v___y_2867_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_2872_, lean_object* v_msg_2873_, lean_object* v_declHint_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_2872_, v_msg_2873_, v_declHint_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v_ref_2872_);
return v_res_2878_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2882_, lean_object* v_constName_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2887_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_2888_ = 0;
lean_inc(v_constName_2883_);
v___x_2889_ = l_Lean_MessageData_ofConstName(v_constName_2883_, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2887_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_2882_, v___x_2892_, v_constName_2883_, v___y_2884_, v___y_2885_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2894_, lean_object* v_constName_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_2894_, v_constName_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v_ref_2894_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(lean_object* v_constName_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_ref_2904_; lean_object* v___x_2905_; 
v_ref_2904_ = lean_ctor_get(v___y_2901_, 5);
v___x_2905_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_2904_, v_constName_2900_, v___y_2901_, v___y_2902_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(lean_object* v_constName_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; lean_object* v_env_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; 
v___x_2915_ = lean_st_ref_get(v___y_2913_);
v_env_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_ref(v_env_2916_);
lean_dec(v___x_2915_);
v___x_2917_ = 0;
lean_inc(v_constName_2911_);
v___x_2918_ = l_Lean_Environment_find_x3f(v_env_2916_, v_constName_2911_, v___x_2917_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_2911_, v___y_2912_, v___y_2913_);
return v___x_2919_;
}
else
{
lean_object* v_val_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_constName_2911_);
v_val_2920_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2918_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_val_2920_);
lean_dec(v___x_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 0);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_val_2920_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1___boxed(lean_object* v_constName_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_constName_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2932_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4));
v___x_2943_ = l_Lean_mkConst(v___x_2942_, v___x_2941_);
return v___x_2943_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7));
v___x_2950_ = l_Lean_mkConst(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Lean_Level_ofNat(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17);
v___x_2967_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
return v___x_2968_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18);
v___x_2970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15));
v___x_2971_ = l_Lean_mkConst(v___x_2970_, v___x_2969_);
return v___x_2971_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_box(0);
v___x_2978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20));
v___x_2979_ = l_Lean_mkConst(v___x_2978_, v___x_2977_);
return v___x_2979_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_box(0);
v___x_2987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23));
v___x_2988_ = l_Lean_mkConst(v___x_2987_, v___x_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object* v_declName_2996_, lean_object* v_stx_2997_, lean_object* v_addDeclName_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; uint8_t v___y_3029_; lean_object* v_procExpr_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; uint8_t v___y_3053_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3088_ = lean_unsigned_to_nat(1u);
v___x_3089_ = l_Lean_Syntax_getArg(v_stx_2997_, v___x_3088_);
v___x_3090_ = l_Lean_Syntax_isNone(v___x_3089_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = l_Lean_Syntax_getArg(v___x_3089_, v___x_3091_);
lean_dec(v___x_3089_);
v___x_3093_ = l_Lean_Syntax_getKind(v___x_3092_);
v___x_3094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27));
v___x_3095_ = lean_name_eq(v___x_3093_, v___x_3094_);
lean_dec(v___x_3093_);
v___y_3053_ = v___x_3095_;
goto v___jp_3052_;
}
else
{
lean_dec(v___x_3089_);
v___y_3053_ = v___x_3090_;
goto v___jp_3052_;
}
v___jp_3002_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1));
v___x_3010_ = l_Lean_Name_append(v_declName_2996_, v___x_3009_);
v___x_3011_ = l_Lean_Core_mkFreshUserName(v___x_3010_, v___y_3004_, v___y_3007_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_unsigned_to_nat(3u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
v___x_3015_ = lean_array_push(v___x_3014_, v___y_3003_);
lean_inc_ref(v___y_3008_);
v___x_3016_ = lean_array_push(v___x_3015_, v___y_3008_);
v___x_3017_ = lean_array_push(v___x_3016_, v___y_3006_);
v___x_3018_ = l_Lean_mkAppN(v___y_3005_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Lean_declareBuiltin(v_a_3012_, v___x_3018_, v___y_3004_, v___y_3007_);
return v___x_3019_;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec_ref(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v___y_3003_);
v_a_3020_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3011_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3011_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
v___jp_3028_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = l_Lean_mkConst(v_addDeclName_2998_, v___x_3033_);
lean_inc(v_declName_2996_);
v___x_3035_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_2996_);
if (v___y_3029_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5);
v___y_3003_ = v___x_3035_;
v___y_3004_ = v___y_3031_;
v___y_3005_ = v___x_3034_;
v___y_3006_ = v_procExpr_3030_;
v___y_3007_ = v___y_3032_;
v___y_3008_ = v___x_3036_;
goto v___jp_3002_;
}
else
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8);
v___y_3003_ = v___x_3035_;
v___y_3004_ = v___y_3031_;
v___y_3005_ = v___x_3034_;
v___y_3006_ = v_procExpr_3030_;
v___y_3007_ = v___y_3032_;
v___y_3008_ = v___x_3037_;
goto v___jp_3002_;
}
}
v___jp_3038_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10);
v___x_3043_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_3042_, v___y_3040_, v___y_3041_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
v___jp_3052_:
{
lean_object* v___x_3054_; 
lean_inc(v_declName_2996_);
v___x_3054_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_declName_2996_, v_a_2999_, v_a_3000_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3056_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3056_ = l_Lean_ConstantInfo_type(v_a_3055_);
lean_dec(v_a_3055_);
if (lean_obj_tag(v___x_3056_) == 4)
{
lean_object* v_declName_3057_; 
v_declName_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_declName_3057_);
lean_dec_ref_known(v___x_3056_, 2);
if (lean_obj_tag(v_declName_3057_) == 1)
{
lean_object* v_pre_3058_; 
v_pre_3058_ = lean_ctor_get(v_declName_3057_, 0);
lean_inc(v_pre_3058_);
if (lean_obj_tag(v_pre_3058_) == 1)
{
lean_object* v_pre_3059_; 
v_pre_3059_ = lean_ctor_get(v_pre_3058_, 0);
lean_inc(v_pre_3059_);
if (lean_obj_tag(v_pre_3059_) == 1)
{
lean_object* v_pre_3060_; 
v_pre_3060_ = lean_ctor_get(v_pre_3059_, 0);
lean_inc(v_pre_3060_);
if (lean_obj_tag(v_pre_3060_) == 1)
{
lean_object* v_pre_3061_; 
v_pre_3061_ = lean_ctor_get(v_pre_3060_, 0);
if (lean_obj_tag(v_pre_3061_) == 0)
{
lean_object* v_str_3062_; lean_object* v_str_3063_; lean_object* v_str_3064_; lean_object* v_str_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_str_3062_ = lean_ctor_get(v_declName_3057_, 1);
lean_inc_ref(v_str_3062_);
lean_dec_ref_known(v_declName_3057_, 2);
v_str_3063_ = lean_ctor_get(v_pre_3058_, 1);
lean_inc_ref(v_str_3063_);
lean_dec_ref_known(v_pre_3058_, 2);
v_str_3064_ = lean_ctor_get(v_pre_3059_, 1);
lean_inc_ref(v_str_3064_);
lean_dec_ref_known(v_pre_3059_, 2);
v_str_3065_ = lean_ctor_get(v_pre_3060_, 1);
lean_inc_ref(v_str_3065_);
lean_dec_ref_known(v_pre_3060_, 2);
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_3067_ = lean_string_dec_eq(v_str_3065_, v___x_3066_);
lean_dec_ref(v_str_3065_);
if (v___x_3067_ == 0)
{
lean_dec_ref(v_str_3064_);
lean_dec_ref(v_str_3063_);
lean_dec_ref(v_str_3062_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_3069_ = lean_string_dec_eq(v_str_3064_, v___x_3068_);
lean_dec_ref(v_str_3064_);
if (v___x_3069_ == 0)
{
lean_dec_ref(v_str_3063_);
lean_dec_ref(v_str_3062_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11));
v___x_3071_ = lean_string_dec_eq(v_str_3063_, v___x_3070_);
lean_dec_ref(v_str_3063_);
if (v___x_3071_ == 0)
{
lean_dec_ref(v_str_3062_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12));
v___x_3073_ = lean_string_dec_eq(v_str_3062_, v___x_3072_);
lean_dec_ref(v_str_3062_);
if (v___x_3073_ == 0)
{
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19);
v___x_3076_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21);
v___x_3077_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24);
lean_inc(v_declName_2996_);
v___x_3078_ = l_Lean_mkConst(v_declName_2996_, v___x_3074_);
v___x_3079_ = l_Lean_mkApp3(v___x_3075_, v___x_3076_, v___x_3077_, v___x_3078_);
v___y_3029_ = v___y_3053_;
v_procExpr_3030_ = v___x_3079_;
v___y_3031_ = v_a_2999_;
v___y_3032_ = v_a_3000_;
goto v___jp_3028_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3060_, 2);
lean_dec_ref_known(v_pre_3059_, 2);
lean_dec_ref_known(v_pre_3058_, 2);
lean_dec_ref_known(v_declName_3057_, 2);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_dec(v_pre_3060_);
lean_dec_ref_known(v_pre_3059_, 2);
lean_dec_ref_known(v_pre_3058_, 2);
lean_dec_ref_known(v_declName_3057_, 2);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_dec_ref_known(v_pre_3058_, 2);
lean_dec(v_pre_3059_);
lean_dec_ref_known(v_declName_3057_, 2);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_dec_ref_known(v_declName_3057_, 2);
lean_dec(v_pre_3058_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_dec(v_declName_3057_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_dec_ref(v___x_3056_);
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v___y_3039_ = v___y_3053_;
v___y_3040_ = v_a_2999_;
v___y_3041_ = v_a_3000_;
goto v___jp_3038_;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_addDeclName_2998_);
lean_dec(v_declName_2996_);
v_a_3080_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3054_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3054_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object* v_declName_3096_, lean_object* v_stx_3097_, lean_object* v_addDeclName_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_3096_, v_stx_3097_, v_addDeclName_3098_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_stx_3097_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(lean_object* v_00_u03b1_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_3104_, v___y_3105_, v___y_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___boxed(lean_object* v_00_u03b1_3109_, lean_object* v_msg_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(v_00_u03b1_3109_, v_msg_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(lean_object* v_00_u03b1_3115_, lean_object* v_constName_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_3116_, v___y_3117_, v___y_3118_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3121_, lean_object* v_constName_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(v_00_u03b1_3121_, v_constName_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3127_, lean_object* v_ref_3128_, lean_object* v_constName_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_3128_, v_constName_3129_, v___y_3130_, v___y_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_ref_3135_, lean_object* v_constName_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(v_00_u03b1_3134_, v_ref_3135_, v_constName_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_ref_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_3141_, lean_object* v_ref_3142_, lean_object* v_msg_3143_, lean_object* v_declHint_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_3142_, v_msg_3143_, v_declHint_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_ref_3150_, lean_object* v_msg_3151_, lean_object* v_declHint_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_3149_, v_ref_3150_, v_msg_3151_, v_declHint_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v_ref_3150_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3157_, lean_object* v_declHint_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_3157_, v_declHint_3158_, v___y_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3163_, lean_object* v_declHint_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_3163_, v_declHint_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_3169_, lean_object* v_ref_3170_, lean_object* v_msg_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_3170_, v_msg_3171_, v___y_3172_, v___y_3173_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_ref_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_3176_, v_ref_3177_, v_msg_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_ref_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object* v_declName_3183_, uint8_t v_post_3184_, lean_object* v_proc_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_3188_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_3187_, v_declName_3183_, v_post_3184_, v_proc_3185_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object* v_declName_3189_, lean_object* v_post_3190_, lean_object* v_proc_3191_, lean_object* v_a_3192_){
_start:
{
uint8_t v_post_boxed_3193_; lean_object* v_res_3194_; 
v_post_boxed_3193_ = lean_unbox(v_post_3190_);
v_res_3194_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(v_declName_3189_, v_post_boxed_3193_, v_proc_3191_);
return v_res_3194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v_x_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_);
v___x_3203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_3202_, v___y_3199_, v___y_3200_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_x_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v_x_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v_x_3204_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_declName_3215_, lean_object* v_stx_3216_, uint8_t v_x_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_3222_ = l_Lean_Name_mkStr6(v___x_3210_, v___x_3211_, v___x_3212_, v___x_3213_, v___x_3214_, v___x_3221_);
v___x_3223_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_3215_, v_stx_3216_, v___x_3222_, v___y_3218_, v___y_3219_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v___x_3224_, lean_object* v___x_3225_, lean_object* v___x_3226_, lean_object* v___x_3227_, lean_object* v___x_3228_, lean_object* v_declName_3229_, lean_object* v_stx_3230_, lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
uint8_t v_x_164__boxed_3235_; lean_object* v_res_3236_; 
v_x_164__boxed_3235_ = lean_unbox(v_x_3231_);
v_res_3236_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v___x_3224_, v___x_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v_declName_3229_, v_stx_3230_, v_x_164__boxed_3235_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v_stx_3230_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_3271_ = l_Lean_registerBuiltinAttribute(v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_a_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
return v_res_3273_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver);
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalTermSolverMode);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprSolverMode);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_instEvalExprBVDecideConfig);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
