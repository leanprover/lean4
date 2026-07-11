// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Attr
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Simp public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.Simp.Theorems import Lean.Elab.ConfigEval import Lean.Meta.Sym.Simp.Attr
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__11_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 74, 81, 238, 190, 83, 40, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__11_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__11_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__12_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__12_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__12_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__13_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__11_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__12_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 168, 70, 51, 34, 197, 207, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__13_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__13_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__14_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__13_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(83, 157, 105, 18, 233, 221, 67, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__14_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__14_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__15_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__14_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 191, 49, 237, 158, 103, 104, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__15_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__15_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__16_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__15_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 59, 172, 202, 76, 35, 108, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__16_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__16_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__17_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__16_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 65, 70, 188, 24, 122, 189, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__17_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__17_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__18_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__17_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 226, 119, 164, 163, 224, 214, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__18_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__18_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__19_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__19_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__19_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__20_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__18_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__19_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 148, 210, 21, 237, 181, 86, 93)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__20_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__20_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__21_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__21_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__21_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__22_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__20_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__21_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 62, 204, 15, 190, 84, 170, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__22_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__22_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__23_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__22_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 220, 112, 65, 205, 180, 77, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__23_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__23_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__24_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__23_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 15, 70, 14, 244, 111, 57, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__24_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__24_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__25_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__24_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 110, 38, 9, 108, 94, 133, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__25_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__25_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__26_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__25_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 245, 249, 252, 230, 214, 105, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__26_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__26_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__26_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__12_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 2, 60, 20, 173, 28, 105, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__28_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(921759773) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(81, 112, 125, 234, 15, 167, 169, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__28_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__28_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__30_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__28_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 248, 163, 40, 189, 30, 248, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__30_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__30_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__32_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__30_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 126, 52, 95, 240, 88, 70, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__32_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__32_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__33_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__32_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(239, 163, 99, 74, 157, 5, 67, 76)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__33_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__33_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "solver"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 159, 50, 22, 96, 145, 4, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 158, 105, 178, 36, 68, 6, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 500, .m_capacity = 500, .m_length = 499, .m_data = "Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n\n     1. If this is set to something besides the empty string they will use that binary.\n\n     2. If this is set to the empty string they will check if there is a cadical binary next to theexecuting program. Usually that program is going to be `lean` itself and we do ship a`cadical` next to it.\n\n     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicatesto use the one that ships with Lean."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 17, 192, 221, 253, 74, 142, 34)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(241, 175, 205, 20, 182, 132, 223, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_sat_solver;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "counterexample"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "SolverMode"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___boxed, .m_arity = 14, .m_num_fixed = 5, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__1_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 234, 163, 101, 135, 19, 78, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode;
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BVDecideConfig"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig;
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "graphviz"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "solverMode"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeout"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "trimProofs"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(185, 35, 170, 33, 56, 163, 92, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(138, 62, 200, 17, 191, 250, 20, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(172, 213, 62, 248, 144, 193, 119, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 180, 226, 180, 157, 207, 20, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "shortCircuit"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 98, 5, 93, 176, 49, 199, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(57, 132, 100, 173, 170, 111, 204, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(33, 94, 75, 99, 14, 104, 154, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "embeddedConstraintSubst"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enums"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixedInt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(70, 215, 84, 227, 237, 239, 174, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(100, 69, 255, 25, 239, 243, 175, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(31, 99, 203, 82, 4, 19, 166, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "acNf"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "andFlattening"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binaryProofs"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(92, 177, 215, 204, 53, 6, 208, 155)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(50, 143, 191, 247, 230, 85, 201, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(209, 218, 38, 182, 3, 205, 122, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "simp theorems used by bv_normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bvNormalizeExt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 148, 199, 156, 241, 6, 144, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "int_toBitVec_sym"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 183, 198, 233, 28, 225, 9, 44)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "int_toBitVec_meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 102, 155, 59, 8, 117, 187, 135)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "sym simp theorems used to convert UIntX/IntX statements into BitVec ones"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "symIntToBitVecExt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 93, 154, 6, 69, 19, 79, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_symIntToBitVecExt;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "meta simp theorems used to convert UIntX/IntX statements into BitVec ones"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "metaIntToBitVecExt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 239, 95, 192, 12, 44, 254, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(846454893) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 110, 84, 183, 42, 126, 189, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 250, 140, 161, 122, 59, 171, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 247, 90, 34, 175, 78, 129, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(118, 130, 162, 92, 24, 91, 41, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "simp theorems used to convert UIntX/IntX statements into BitVec ones"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_builtinBVNormalizeSimprocsRef;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "bv_normalize_proc"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 55, 180, 228, 60, 0, 67, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "simprocs used by bv_normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bvNormalizeSimprocExt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 44, 162, 241, 57, 49, 121, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected type at bv_normalize simproc"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__14_value),LEAN_SCALAR_PTR_LITERAL(236, 33, 85, 75, 207, 191, 2, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__12_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__22_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__26_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Not implemented yet, [-builtin_bv_normalize_proc]"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "addBVNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1562260944) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(105, 231, 12, 82, 128, 106, 199, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 89, 146, 118, 184, 45, 135, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(6, 22, 247, 58, 1, 69, 124, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(7, 170, 91, 178, 97, 250, 148, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "bvNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 5, 36, 101, 149, 10, 160, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Builtin bv_normalize simproc"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__7_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__8_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__9_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_84_ = 0;
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__33_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_86_ = l_Lean_registerTraceClass(v___x_83_, v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2____boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_();
return v_res_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(3575118154u);
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_96_ = l_Lean_Name_num___override(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_98_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_99_ = l_Lean_Name_str___override(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_101_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_102_ = l_Lean_Name_str___override(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_105_ = l_Lean_Name_num___override(v___x_104_, v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_));
v___x_108_ = 0;
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_110_ = l_Lean_registerTraceClass(v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object* v_name_113_, lean_object* v_decl_114_, lean_object* v_ref_115_){
_start:
{
lean_object* v_defValue_117_; lean_object* v_descr_118_; lean_object* v_deprecation_x3f_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_defValue_117_ = lean_ctor_get(v_decl_114_, 0);
v_descr_118_ = lean_ctor_get(v_decl_114_, 1);
v_deprecation_x3f_119_ = lean_ctor_get(v_decl_114_, 2);
lean_inc(v_defValue_117_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v_defValue_117_);
lean_inc(v_deprecation_x3f_119_);
lean_inc_ref(v_descr_118_);
lean_inc_n(v_name_113_, 2);
v___x_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_121_, 0, v_name_113_);
lean_ctor_set(v___x_121_, 1, v_ref_115_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_ctor_set(v___x_121_, 3, v_descr_118_);
lean_ctor_set(v___x_121_, 4, v_deprecation_x3f_119_);
v___x_122_ = lean_register_option(v_name_113_, v___x_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_131_);
v___x_124_ = v___x_122_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_dec(v___x_122_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
lean_inc(v_defValue_117_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v_name_113_);
lean_ctor_set(v___x_126_, 1, v_defValue_117_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec(v_name_113_);
v_a_132_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_122_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_140_, lean_object* v_decl_141_, lean_object* v_ref_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_140_, v_decl_141_, v_ref_142_);
lean_dec_ref(v_decl_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_166_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v___x_163_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v___x_170_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(lean_object* v_00_u03b1_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(v_00_u03b1_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(lean_object* v___x_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_ctor_203_, lean_object* v_args_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_213_ = lean_string_dec_eq(v_ctor_203_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_215_ = lean_string_dec_eq(v_ctor_203_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_217_ = lean_string_dec_eq(v_ctor_203_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v___x_198_);
v___x_218_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = l_Lean_Name_mkStr6(v___x_198_, v___x_199_, v___x_200_, v___x_201_, v___x_202_, v___x_216_);
v___x_220_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_219_);
v___x_221_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_219_, v___x_220_, v_args_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_233_; 
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v___x_221_, 0);
lean_dec(v_unused_234_);
v___x_223_ = v___x_221_;
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
else
{
lean_dec(v___x_221_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_225_ = 0;
v___x_226_ = lean_box(0);
v___x_227_ = l_Lean_Expr_const___override(v___x_219_, v___x_226_);
v___x_228_ = lean_box(v___x_225_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_231_ = v___x_223_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v___x_219_);
v_a_235_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_221_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_221_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = l_Lean_Name_mkStr6(v___x_198_, v___x_199_, v___x_200_, v___x_201_, v___x_202_, v___x_214_);
v___x_244_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_243_);
v___x_245_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_243_, v___x_244_, v_args_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_257_; 
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_245_, 0);
lean_dec(v_unused_258_);
v___x_247_ = v___x_245_;
v_isShared_248_ = v_isSharedCheck_257_;
goto v_resetjp_246_;
}
else
{
lean_dec(v___x_245_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_257_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_249_ = 2;
v___x_250_ = lean_box(0);
v___x_251_ = l_Lean_Expr_const___override(v___x_243_, v___x_250_);
v___x_252_ = lean_box(v___x_249_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_253_);
v___x_255_ = v___x_247_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v___x_243_);
v_a_259_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_245_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_245_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = l_Lean_Name_mkStr6(v___x_198_, v___x_199_, v___x_200_, v___x_201_, v___x_202_, v___x_212_);
v___x_268_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_267_);
v___x_269_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_267_, v___x_268_, v_args_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_282_);
v___x_271_ = v___x_269_;
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___x_269_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_273_ = 1;
v___x_274_ = lean_box(0);
v___x_275_ = l_Lean_Expr_const___override(v___x_267_, v___x_274_);
v___x_276_ = lean_box(v___x_273_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_277_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v___x_267_);
v_a_283_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_269_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_269_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v___x_293_, lean_object* v___x_294_, lean_object* v___x_295_, lean_object* v_ctor_296_, lean_object* v_args_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(v___x_291_, v___x_292_, v___x_293_, v___x_294_, v___x_295_, v_ctor_296_, v_args_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec_ref(v_args_297_);
lean_dec_ref(v_ctor_296_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___f_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2));
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_330_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_329_, v___f_328_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___boxed(lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_343_ = l_Lean_Expr_const___override(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0));
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(lean_object* v_00_u03b1_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(v_00_u03b1_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v___x_378_; lean_object* v_mctx_379_; lean_object* v_lctx_380_; lean_object* v_options_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = lean_st_ref_get(v___y_372_);
v_mctx_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc_ref(v_mctx_379_);
lean_dec(v___x_378_);
v_lctx_380_ = lean_ctor_get(v___y_371_, 2);
v_options_381_ = lean_ctor_get(v___y_373_, 2);
lean_inc_ref(v_options_381_);
lean_inc_ref(v_lctx_380_);
v___x_382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_382_, 0, v_env_377_);
lean_ctor_set(v___x_382_, 1, v_mctx_379_);
lean_ctor_set(v___x_382_, 2, v_lctx_380_);
lean_ctor_set(v___x_382_, 3, v_options_381_);
v___x_383_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_msgData_370_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_ref_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_ref_398_ = lean_ctor_get(v___y_395_, 5);
v___x_399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_inc(v_ref_398_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_ref_398_);
lean_ctor_set(v___x_404_, 1, v_a_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 1);
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_419_, lean_object* v_args_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_439_ = lean_string_dec_eq(v_ctor_419_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_441_ = lean_string_dec_eq(v_ctor_419_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_443_ = lean_string_dec_eq(v_ctor_419_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_array_get_size(v_args_420_);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_nat_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_448_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
goto v___jp_426_;
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_array_get_size(v_args_420_);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_nat_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_462_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_461_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
goto v___jp_430_;
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_array_get_size(v_args_420_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_475_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_474_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
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
goto v___jp_434_;
}
}
v___jp_426_:
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = 0;
v___x_428_ = lean_box(v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
v___jp_430_:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = 2;
v___x_432_ = lean_box(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
v___jp_434_:
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 1;
v___x_436_ = lean_box(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_484_, lean_object* v_args_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_484_, v_args_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_args_485_);
lean_dec_ref(v_ctor_484_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___f_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___f_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0));
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_501_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_500_, v___f_499_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_509_, lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_517_, v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0));
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v_ctor_533_, lean_object* v_args_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_718_ = lean_string_dec_eq(v_ctor_533_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_array_get_size(v_args_534_);
v___x_721_ = lean_unsigned_to_nat(13u);
v___x_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v___x_723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_724_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_723_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
goto v___jp_540_;
}
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = l_Lean_instInhabitedExpr;
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_542_);
lean_inc(v___x_543_);
v___x_544_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_543_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_546_);
lean_inc(v___x_547_);
v___x_548_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_547_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_550_);
lean_inc(v___x_551_);
v___x_552_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_551_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_554_);
lean_inc(v___x_555_);
v___x_556_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_555_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_unsigned_to_nat(4u);
v___x_559_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_558_);
lean_inc(v___x_559_);
v___x_560_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_559_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = lean_unsigned_to_nat(5u);
v___x_563_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_562_);
lean_inc(v___x_563_);
v___x_564_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_563_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = lean_unsigned_to_nat(6u);
v___x_567_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_566_);
lean_inc(v___x_567_);
v___x_568_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_567_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_unsigned_to_nat(7u);
v___x_571_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_570_);
lean_inc(v___x_571_);
v___x_572_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_571_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_unsigned_to_nat(8u);
v___x_575_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_574_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_575_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = lean_unsigned_to_nat(9u);
v___x_579_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_578_);
lean_inc(v___x_579_);
v___x_580_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_579_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_unsigned_to_nat(10u);
v___x_583_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_582_);
lean_inc(v___x_583_);
v___x_584_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_583_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_unsigned_to_nat(11u);
v___x_587_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_586_);
lean_inc(v___x_587_);
v___x_588_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_587_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_unsigned_to_nat(12u);
v___x_591_ = lean_array_get_borrowed(v___x_541_, v_args_534_, v___x_590_);
lean_inc(v___x_591_);
v___x_592_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v___x_591_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_612_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; uint8_t v___x_598_; uint8_t v___x_599_; uint8_t v___x_600_; uint8_t v___x_601_; uint8_t v___x_602_; uint8_t v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; uint8_t v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_610_; 
v___x_597_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_597_, 0, v_a_545_);
lean_ctor_set(v___x_597_, 1, v_a_585_);
v___x_598_ = lean_unbox(v_a_549_);
lean_dec(v_a_549_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2, v___x_598_);
v___x_599_ = lean_unbox(v_a_553_);
lean_dec(v_a_553_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 1, v___x_599_);
v___x_600_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 2, v___x_600_);
v___x_601_ = lean_unbox(v_a_561_);
lean_dec(v_a_561_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 3, v___x_601_);
v___x_602_ = lean_unbox(v_a_565_);
lean_dec(v_a_565_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 4, v___x_602_);
v___x_603_ = lean_unbox(v_a_569_);
lean_dec(v_a_569_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 5, v___x_603_);
v___x_604_ = lean_unbox(v_a_573_);
lean_dec(v_a_573_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 6, v___x_604_);
v___x_605_ = lean_unbox(v_a_577_);
lean_dec(v_a_577_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 7, v___x_605_);
v___x_606_ = lean_unbox(v_a_581_);
lean_dec(v_a_581_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 8, v___x_606_);
v___x_607_ = lean_unbox(v_a_589_);
lean_dec(v_a_589_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 9, v___x_607_);
v___x_608_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 10, v___x_608_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_610_ = v___x_595_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_597_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_613_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_592_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_592_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_621_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_588_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_588_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_629_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_584_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_584_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_577_);
lean_dec(v_a_573_);
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_637_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_580_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_580_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_a_573_);
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_645_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_576_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_576_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_569_);
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_653_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_572_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_572_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_565_);
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_661_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_568_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_568_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_561_);
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_669_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_564_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_564_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_677_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_560_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_560_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v_a_553_);
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_685_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_556_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_556_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v_a_549_);
lean_dec(v_a_545_);
v_a_693_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_552_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_552_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_a_545_);
v_a_701_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_548_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_548_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_544_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_544_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_733_, lean_object* v_args_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v_ctor_733_, v_args_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_args_734_);
lean_dec_ref(v_ctor_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___f_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0));
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_757_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_756_, v___f_755_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_box(0);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_768_ = l_Lean_Expr_const___override(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0));
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_box(0);
v___x_776_ = l_Lean_Elab_abortTermExceptionId;
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_782_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(1);
v___x_784_ = l_Lean_MessageData_ofFormat(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_789_ = l_Lean_MessageData_ofFormat(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
return v_x_790_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_815_; 
v_head_792_ = lean_ctor_get(v_x_791_, 0);
v_tail_793_ = lean_ctor_get(v_x_791_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_815_ == 0)
{
v___x_795_ = v_x_791_;
v_isShared_796_ = v_isSharedCheck_815_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_tail_793_);
lean_inc(v_head_792_);
lean_dec(v_x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_815_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_before_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_813_; 
v_before_797_ = lean_ctor_get(v_head_792_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_head_792_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_head_792_, 1);
lean_dec(v_unused_814_);
v___x_799_ = v_head_792_;
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_before_797_);
lean_dec(v_head_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 7);
lean_ctor_set(v___x_799_, 1, v___x_801_);
lean_ctor_set(v___x_799_, 0, v_x_790_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_x_790_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_812_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v___x_804_);
lean_ctor_set(v___x_795_, 0, v___x_803_);
v___x_806_ = v___x_795_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_811_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = l_Lean_MessageData_ofSyntax(v_before_797_);
v___x_808_ = l_Lean_indentD(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v_x_790_ = v___x_809_;
v_x_791_ = v_tail_793_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_816_, lean_object* v_opt_817_){
_start:
{
lean_object* v_name_818_; lean_object* v_defValue_819_; lean_object* v_map_820_; lean_object* v___x_821_; 
v_name_818_ = lean_ctor_get(v_opt_817_, 0);
v_defValue_819_ = lean_ctor_get(v_opt_817_, 1);
v_map_820_ = lean_ctor_get(v_opts_816_, 0);
v___x_821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_820_, v_name_818_);
if (lean_obj_tag(v___x_821_) == 0)
{
uint8_t v___x_822_; 
v___x_822_ = lean_unbox(v_defValue_819_);
return v___x_822_;
}
else
{
lean_object* v_val_823_; 
v_val_823_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v___x_821_, 1);
if (lean_obj_tag(v_val_823_) == 1)
{
uint8_t v_v_824_; 
v_v_824_ = lean_ctor_get_uint8(v_val_823_, 0);
lean_dec_ref_known(v_val_823_, 0);
return v_v_824_;
}
else
{
uint8_t v___x_825_; 
lean_dec(v_val_823_);
v___x_825_ = lean_unbox(v_defValue_819_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_826_, lean_object* v_opt_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_826_, v_opt_827_);
lean_dec_ref(v_opt_827_);
lean_dec_ref(v_opts_826_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_834_ = l_Lean_MessageData_ofFormat(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_835_, lean_object* v_macroStack_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_options_839_; lean_object* v___x_840_; uint8_t v___x_841_; uint8_t v___x_842_; 
v_options_839_ = lean_ctor_get(v___y_837_, 2);
v___x_840_ = l_Lean_Elab_pp_macroStack;
v___x_841_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_options_839_, v___x_840_);
v___x_842_ = lean_bool_not(v___x_841_);
if (v___x_842_ == 0)
{
if (lean_obj_tag(v_macroStack_836_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_msgData_835_);
return v___x_843_;
}
else
{
lean_object* v_head_844_; lean_object* v_after_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_860_; 
v_head_844_ = lean_ctor_get(v_macroStack_836_, 0);
lean_inc(v_head_844_);
v_after_845_ = lean_ctor_get(v_head_844_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_head_844_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_head_844_, 0);
lean_dec(v_unused_861_);
v___x_847_ = v_head_844_;
v_isShared_848_ = v_isSharedCheck_860_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_after_845_);
lean_dec(v_head_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_860_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 7);
lean_ctor_set(v___x_847_, 1, v___x_849_);
lean_ctor_set(v___x_847_, 0, v_msgData_835_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_msgData_835_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_859_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_msgData_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_852_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_MessageData_ofSyntax(v_after_845_);
v___x_855_ = l_Lean_indentD(v___x_854_);
v_msgData_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_856_, 0, v___x_853_);
lean_ctor_set(v_msgData_856_, 1, v___x_855_);
v___x_857_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_856_, v_macroStack_836_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v_macroStack_836_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_msgData_835_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_863_, lean_object* v_macroStack_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_863_, v_macroStack_864_, v___y_865_);
lean_dec_ref(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v_macroStack_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_890_; 
v_ref_876_ = lean_ctor_get(v___y_873_, 5);
v___x_877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_868_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v_macroStack_879_ = lean_ctor_get(v___y_869_, 1);
v___x_880_ = l_Lean_Elab_getBetterRef(v_ref_876_, v_macroStack_879_);
lean_inc(v_macroStack_879_);
v___x_881_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_878_, v_macroStack_879_, v___y_873_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_890_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_880_);
lean_ctor_set(v___x_886_, 1, v_a_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 1);
lean_ctor_set(v___x_884_, 0, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_Expr_hasMVar(v_e_900_);
v___x_904_ = lean_bool_not(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v_mctx_906_; lean_object* v___x_907_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_910_; lean_object* v_cache_911_; lean_object* v_zetaDeltaFVarIds_912_; lean_object* v_postponed_913_; lean_object* v_diag_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_923_; 
v___x_905_ = lean_st_ref_get(v___y_901_);
v_mctx_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_mctx_906_);
lean_dec(v___x_905_);
v___x_907_ = l_Lean_instantiateMVarsCore(v_mctx_906_, v_e_900_);
v_fst_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_fst_908_);
v_snd_909_ = lean_ctor_get(v___x_907_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v___x_907_);
v___x_910_ = lean_st_ref_take(v___y_901_);
v_cache_911_ = lean_ctor_get(v___x_910_, 1);
v_zetaDeltaFVarIds_912_ = lean_ctor_get(v___x_910_, 2);
v_postponed_913_ = lean_ctor_get(v___x_910_, 3);
v_diag_914_ = lean_ctor_get(v___x_910_, 4);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_910_, 0);
lean_dec(v_unused_924_);
v___x_916_ = v___x_910_;
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_diag_914_);
lean_inc(v_postponed_913_);
lean_inc(v_zetaDeltaFVarIds_912_);
lean_inc(v_cache_911_);
lean_dec(v___x_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_snd_909_);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_snd_909_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_cache_911_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_zetaDeltaFVarIds_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_postponed_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_diag_914_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_st_ref_set(v___y_901_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v_fst_908_);
return v___x_921_;
}
}
}
else
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_e_900_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_926_, v___y_927_);
lean_dec(v___y_927_);
return v_res_929_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_934_ = l_Lean_MessageData_ofExpr(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_936_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_942_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_ty_x3f_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_fileName_964_; lean_object* v_fileMap_965_; lean_object* v_options_966_; lean_object* v_currRecDepth_967_; lean_object* v_maxRecDepth_968_; lean_object* v_ref_969_; lean_object* v_currNamespace_970_; lean_object* v_openDecls_971_; lean_object* v_initHeartbeats_972_; lean_object* v_maxHeartbeats_973_; lean_object* v_quotContext_974_; lean_object* v_currMacroScope_975_; uint8_t v_diag_976_; lean_object* v_cancelTk_x3f_977_; uint8_t v_suppressElabErrors_978_; lean_object* v_inheritedTraceOptions_979_; uint8_t v___x_980_; lean_object* v_ref_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_ty_x3f_958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_959_ = 1;
v___x_960_ = lean_box(0);
v___x_961_ = lean_box(v___x_959_);
v___x_962_ = lean_box(v___x_959_);
lean_inc(v_stx_950_);
v___x_963_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_963_, 0, v_stx_950_);
lean_closure_set(v___x_963_, 1, v_ty_x3f_958_);
lean_closure_set(v___x_963_, 2, v___x_961_);
lean_closure_set(v___x_963_, 3, v___x_962_);
lean_closure_set(v___x_963_, 4, v___x_960_);
v_fileName_964_ = lean_ctor_get(v_a_955_, 0);
v_fileMap_965_ = lean_ctor_get(v_a_955_, 1);
v_options_966_ = lean_ctor_get(v_a_955_, 2);
v_currRecDepth_967_ = lean_ctor_get(v_a_955_, 3);
v_maxRecDepth_968_ = lean_ctor_get(v_a_955_, 4);
v_ref_969_ = lean_ctor_get(v_a_955_, 5);
v_currNamespace_970_ = lean_ctor_get(v_a_955_, 6);
v_openDecls_971_ = lean_ctor_get(v_a_955_, 7);
v_initHeartbeats_972_ = lean_ctor_get(v_a_955_, 8);
v_maxHeartbeats_973_ = lean_ctor_get(v_a_955_, 9);
v_quotContext_974_ = lean_ctor_get(v_a_955_, 10);
v_currMacroScope_975_ = lean_ctor_get(v_a_955_, 11);
v_diag_976_ = lean_ctor_get_uint8(v_a_955_, sizeof(void*)*14);
v_cancelTk_x3f_977_ = lean_ctor_get(v_a_955_, 12);
v_suppressElabErrors_978_ = lean_ctor_get_uint8(v_a_955_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_979_ = lean_ctor_get(v_a_955_, 13);
v___x_980_ = 1;
v_ref_981_ = l_Lean_replaceRef(v_stx_950_, v_ref_969_);
lean_dec(v_stx_950_);
lean_inc_ref(v_inheritedTraceOptions_979_);
lean_inc(v_cancelTk_x3f_977_);
lean_inc(v_currMacroScope_975_);
lean_inc(v_quotContext_974_);
lean_inc(v_maxHeartbeats_973_);
lean_inc(v_initHeartbeats_972_);
lean_inc(v_openDecls_971_);
lean_inc(v_currNamespace_970_);
lean_inc(v_maxRecDepth_968_);
lean_inc(v_currRecDepth_967_);
lean_inc_ref(v_options_966_);
lean_inc_ref(v_fileMap_965_);
lean_inc_ref(v_fileName_964_);
v___x_982_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_982_, 0, v_fileName_964_);
lean_ctor_set(v___x_982_, 1, v_fileMap_965_);
lean_ctor_set(v___x_982_, 2, v_options_966_);
lean_ctor_set(v___x_982_, 3, v_currRecDepth_967_);
lean_ctor_set(v___x_982_, 4, v_maxRecDepth_968_);
lean_ctor_set(v___x_982_, 5, v_ref_981_);
lean_ctor_set(v___x_982_, 6, v_currNamespace_970_);
lean_ctor_set(v___x_982_, 7, v_openDecls_971_);
lean_ctor_set(v___x_982_, 8, v_initHeartbeats_972_);
lean_ctor_set(v___x_982_, 9, v_maxHeartbeats_973_);
lean_ctor_set(v___x_982_, 10, v_quotContext_974_);
lean_ctor_set(v___x_982_, 11, v_currMacroScope_975_);
lean_ctor_set(v___x_982_, 12, v_cancelTk_x3f_977_);
lean_ctor_set(v___x_982_, 13, v_inheritedTraceOptions_979_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*14, v_diag_976_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*14 + 1, v_suppressElabErrors_978_);
v___x_983_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_963_, v___x_980_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v___x_982_, v_a_956_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; uint8_t v___y_997_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___x_1081_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_984_, v_a_954_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_1081_ = l_Lean_Expr_hasSorry(v_a_986_);
if (v___x_1081_ == 0)
{
v___y_1026_ = v_a_951_;
v___y_1027_ = v_a_952_;
v___y_1028_ = v_a_953_;
v___y_1029_ = v_a_954_;
v___y_1030_ = v___x_982_;
v___y_1031_ = v_a_956_;
goto v___jp_1025_;
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_Expr_hasSyntheticSorry(v_a_986_);
if (v___x_1082_ == 0)
{
v___y_1063_ = v_a_951_;
v___y_1064_ = v_a_952_;
v___y_1065_ = v_a_953_;
v___y_1066_ = v_a_954_;
v___y_1067_ = v___x_982_;
v___y_1068_ = v_a_956_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_986_);
lean_dec_ref_known(v___x_982_, 14);
v___x_1083_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
v___jp_987_:
{
if (v___y_997_ == 0)
{
if (lean_obj_tag(v___y_993_) == 0)
{
lean_dec_ref_known(v___y_993_, 2);
lean_dec_ref(v___y_995_);
lean_dec(v_a_986_);
return v___y_992_;
}
else
{
lean_object* v_id_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_id_998_ = lean_ctor_get(v___y_993_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___y_993_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___y_993_, 1);
lean_dec(v_unused_1012_);
v___x_1000_ = v___y_993_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_id_998_);
lean_dec(v___y_993_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
uint8_t v___x_1002_; 
v___x_1002_ = l_Lean_instBEqInternalExceptionId_beq(v___y_990_, v_id_998_);
lean_dec(v_id_998_);
if (v___x_1002_ == 0)
{
lean_del_object(v___x_1000_);
lean_dec_ref(v___y_995_);
lean_dec(v_a_986_);
return v___y_992_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec_ref(v___y_992_);
v___x_1003_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_1004_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1005_ = l_Lean_indentExpr(v_a_986_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 7);
lean_ctor_set(v___x_1000_, 1, v___x_1005_);
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1007_ = v___x_1000_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1003_);
v___x_1009_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1008_, v___y_996_, v___y_994_, v___y_989_, v___y_988_, v___y_995_, v___y_991_);
lean_dec_ref(v___y_995_);
return v___x_1009_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_995_);
lean_dec_ref(v___y_993_);
lean_dec(v_a_986_);
return v___y_992_;
}
}
v___jp_1013_:
{
lean_object* v___x_1020_; 
lean_inc(v_a_986_);
v___x_1020_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_986_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_dec_ref(v___y_1018_);
lean_dec(v_a_986_);
return v___x_1020_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
v___x_1022_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1023_ = l_Lean_Exception_isInterrupt(v_a_1021_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; 
lean_inc(v_a_1021_);
v___x_1024_ = l_Lean_Exception_isRuntime(v_a_1021_);
v___y_988_ = v___y_1017_;
v___y_989_ = v___y_1016_;
v___y_990_ = v___x_1022_;
v___y_991_ = v___y_1019_;
v___y_992_ = v___x_1020_;
v___y_993_ = v_a_1021_;
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1018_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___x_1024_;
goto v___jp_987_;
}
else
{
v___y_988_ = v___y_1017_;
v___y_989_ = v___y_1016_;
v___y_990_ = v___x_1022_;
v___y_991_ = v___y_1019_;
v___y_992_ = v___x_1020_;
v___y_993_ = v_a_1021_;
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1018_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___x_1023_;
goto v___jp_987_;
}
}
}
v___jp_1025_:
{
lean_object* v___x_1032_; 
lean_inc(v_a_986_);
v___x_1032_ = l_Lean_Meta_getMVars(v_a_986_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1033_, v___x_960_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v_a_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; uint8_t v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = lean_unbox(v_a_1035_);
lean_dec(v_a_1035_);
if (v___x_1036_ == 0)
{
v___y_1014_ = v___y_1026_;
v___y_1015_ = v___y_1027_;
v___y_1016_ = v___y_1028_;
v___y_1017_ = v___y_1029_;
v___y_1018_ = v___y_1030_;
v___y_1019_ = v___y_1031_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___y_1030_);
lean_dec(v_a_986_);
v___x_1037_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v___y_1030_);
lean_dec(v_a_986_);
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___y_1030_);
lean_dec(v_a_986_);
v_a_1054_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1032_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1032_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v___x_1069_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1070_ = l_Lean_indentExpr(v_a_986_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1071_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v___y_1067_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref_known(v___x_982_, 14);
v_a_1092_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_983_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_983_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_1110_ = l_Lean_MessageData_ofExpr(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1112_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1115_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_ty_x3f_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_fileName_1131_; lean_object* v_fileMap_1132_; lean_object* v_options_1133_; lean_object* v_currRecDepth_1134_; lean_object* v_maxRecDepth_1135_; lean_object* v_ref_1136_; lean_object* v_currNamespace_1137_; lean_object* v_openDecls_1138_; lean_object* v_initHeartbeats_1139_; lean_object* v_maxHeartbeats_1140_; lean_object* v_quotContext_1141_; lean_object* v_currMacroScope_1142_; uint8_t v_diag_1143_; lean_object* v_cancelTk_x3f_1144_; uint8_t v_suppressElabErrors_1145_; lean_object* v_inheritedTraceOptions_1146_; uint8_t v___x_1147_; lean_object* v_ref_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_ty_x3f_1125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_1126_ = 1;
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_box(v___x_1126_);
v___x_1129_ = lean_box(v___x_1126_);
lean_inc(v_stx_1117_);
v___x_1130_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1130_, 0, v_stx_1117_);
lean_closure_set(v___x_1130_, 1, v_ty_x3f_1125_);
lean_closure_set(v___x_1130_, 2, v___x_1128_);
lean_closure_set(v___x_1130_, 3, v___x_1129_);
lean_closure_set(v___x_1130_, 4, v___x_1127_);
v_fileName_1131_ = lean_ctor_get(v_a_1122_, 0);
v_fileMap_1132_ = lean_ctor_get(v_a_1122_, 1);
v_options_1133_ = lean_ctor_get(v_a_1122_, 2);
v_currRecDepth_1134_ = lean_ctor_get(v_a_1122_, 3);
v_maxRecDepth_1135_ = lean_ctor_get(v_a_1122_, 4);
v_ref_1136_ = lean_ctor_get(v_a_1122_, 5);
v_currNamespace_1137_ = lean_ctor_get(v_a_1122_, 6);
v_openDecls_1138_ = lean_ctor_get(v_a_1122_, 7);
v_initHeartbeats_1139_ = lean_ctor_get(v_a_1122_, 8);
v_maxHeartbeats_1140_ = lean_ctor_get(v_a_1122_, 9);
v_quotContext_1141_ = lean_ctor_get(v_a_1122_, 10);
v_currMacroScope_1142_ = lean_ctor_get(v_a_1122_, 11);
v_diag_1143_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*14);
v_cancelTk_x3f_1144_ = lean_ctor_get(v_a_1122_, 12);
v_suppressElabErrors_1145_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1146_ = lean_ctor_get(v_a_1122_, 13);
v___x_1147_ = 1;
v_ref_1148_ = l_Lean_replaceRef(v_stx_1117_, v_ref_1136_);
lean_dec(v_stx_1117_);
lean_inc_ref(v_inheritedTraceOptions_1146_);
lean_inc(v_cancelTk_x3f_1144_);
lean_inc(v_currMacroScope_1142_);
lean_inc(v_quotContext_1141_);
lean_inc(v_maxHeartbeats_1140_);
lean_inc(v_initHeartbeats_1139_);
lean_inc(v_openDecls_1138_);
lean_inc(v_currNamespace_1137_);
lean_inc(v_maxRecDepth_1135_);
lean_inc(v_currRecDepth_1134_);
lean_inc_ref(v_options_1133_);
lean_inc_ref(v_fileMap_1132_);
lean_inc_ref(v_fileName_1131_);
v___x_1149_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1149_, 0, v_fileName_1131_);
lean_ctor_set(v___x_1149_, 1, v_fileMap_1132_);
lean_ctor_set(v___x_1149_, 2, v_options_1133_);
lean_ctor_set(v___x_1149_, 3, v_currRecDepth_1134_);
lean_ctor_set(v___x_1149_, 4, v_maxRecDepth_1135_);
lean_ctor_set(v___x_1149_, 5, v_ref_1148_);
lean_ctor_set(v___x_1149_, 6, v_currNamespace_1137_);
lean_ctor_set(v___x_1149_, 7, v_openDecls_1138_);
lean_ctor_set(v___x_1149_, 8, v_initHeartbeats_1139_);
lean_ctor_set(v___x_1149_, 9, v_maxHeartbeats_1140_);
lean_ctor_set(v___x_1149_, 10, v_quotContext_1141_);
lean_ctor_set(v___x_1149_, 11, v_currMacroScope_1142_);
lean_ctor_set(v___x_1149_, 12, v_cancelTk_x3f_1144_);
lean_ctor_set(v___x_1149_, 13, v_inheritedTraceOptions_1146_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*14, v_diag_1143_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*14 + 1, v_suppressElabErrors_1145_);
v___x_1150_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1130_, v___x_1147_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v___x_1149_, v_a_1123_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___x_1248_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1151_, v_a_1121_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
v___x_1248_ = l_Lean_Expr_hasSorry(v_a_1153_);
if (v___x_1248_ == 0)
{
v___y_1193_ = v_a_1118_;
v___y_1194_ = v_a_1119_;
v___y_1195_ = v_a_1120_;
v___y_1196_ = v_a_1121_;
v___y_1197_ = v___x_1149_;
v___y_1198_ = v_a_1123_;
goto v___jp_1192_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_Expr_hasSyntheticSorry(v_a_1153_);
if (v___x_1249_ == 0)
{
v___y_1230_ = v_a_1118_;
v___y_1231_ = v_a_1119_;
v___y_1232_ = v_a_1120_;
v___y_1233_ = v_a_1121_;
v___y_1234_ = v___x_1149_;
v___y_1235_ = v_a_1123_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1153_);
lean_dec_ref_known(v___x_1149_, 14);
v___x_1250_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
v___jp_1154_:
{
if (v___y_1164_ == 0)
{
if (lean_obj_tag(v___y_1160_) == 0)
{
lean_dec_ref_known(v___y_1160_, 2);
lean_dec_ref(v___y_1162_);
lean_dec(v_a_1153_);
return v___y_1163_;
}
else
{
lean_object* v_id_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1178_; 
v_id_1165_ = lean_ctor_get(v___y_1160_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___y_1160_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___y_1160_, 1);
lean_dec(v_unused_1179_);
v___x_1167_ = v___y_1160_;
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_id_1165_);
lean_dec(v___y_1160_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; 
v___x_1169_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1157_, v_id_1165_);
lean_dec(v_id_1165_);
if (v___x_1169_ == 0)
{
lean_del_object(v___x_1167_);
lean_dec_ref(v___y_1162_);
lean_dec(v_a_1153_);
return v___y_1163_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
lean_dec_ref(v___y_1163_);
v___x_1170_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1171_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1172_ = l_Lean_indentExpr(v_a_1153_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 7);
lean_ctor_set(v___x_1167_, 1, v___x_1172_);
lean_ctor_set(v___x_1167_, 0, v___x_1171_);
v___x_1174_ = v___x_1167_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___x_1170_);
v___x_1176_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1175_, v___y_1156_, v___y_1159_, v___y_1158_, v___y_1161_, v___y_1162_, v___y_1155_);
lean_dec_ref(v___y_1162_);
return v___x_1176_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1162_);
lean_dec_ref(v___y_1160_);
lean_dec(v_a_1153_);
return v___y_1163_;
}
}
v___jp_1180_:
{
lean_object* v___x_1187_; 
lean_inc(v_a_1153_);
v___x_1187_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_1153_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref(v___y_1185_);
lean_dec(v_a_1153_);
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
v___x_1189_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1190_ = l_Lean_Exception_isInterrupt(v_a_1188_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; 
lean_inc(v_a_1188_);
v___x_1191_ = l_Lean_Exception_isRuntime(v_a_1188_);
v___y_1155_ = v___y_1186_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___x_1189_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___y_1182_;
v___y_1160_ = v_a_1188_;
v___y_1161_ = v___y_1184_;
v___y_1162_ = v___y_1185_;
v___y_1163_ = v___x_1187_;
v___y_1164_ = v___x_1191_;
goto v___jp_1154_;
}
else
{
v___y_1155_ = v___y_1186_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___x_1189_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___y_1182_;
v___y_1160_ = v_a_1188_;
v___y_1161_ = v___y_1184_;
v___y_1162_ = v___y_1185_;
v___y_1163_ = v___x_1187_;
v___y_1164_ = v___x_1190_;
goto v___jp_1154_;
}
}
}
v___jp_1192_:
{
lean_object* v___x_1199_; 
lean_inc(v_a_1153_);
v___x_1199_ = l_Lean_Meta_getMVars(v_a_1153_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1200_, v___x_1127_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v_a_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; uint8_t v___x_1203_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1201_, 1);
v___x_1203_ = lean_unbox(v_a_1202_);
lean_dec(v_a_1202_);
if (v___x_1203_ == 0)
{
v___y_1181_ = v___y_1193_;
v___y_1182_ = v___y_1194_;
v___y_1183_ = v___y_1195_;
v___y_1184_ = v___y_1196_;
v___y_1185_ = v___y_1197_;
v___y_1186_ = v___y_1198_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1204_; lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v___y_1197_);
lean_dec(v_a_1153_);
v___x_1204_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v___y_1197_);
lean_dec(v_a_1153_);
v_a_1213_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1201_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1201_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v___y_1197_);
lean_dec(v_a_1153_);
v_a_1221_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1199_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1199_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
v___jp_1229_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v___x_1236_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1237_ = l_Lean_indentExpr(v_a_1153_);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1238_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v___y_1234_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref_known(v___x_1149_, 14);
v_a_1259_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1150_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1150_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_fileName_1284_; lean_object* v_fileMap_1285_; lean_object* v_options_1286_; lean_object* v_currRecDepth_1287_; lean_object* v_maxRecDepth_1288_; lean_object* v_ref_1289_; lean_object* v_currNamespace_1290_; lean_object* v_openDecls_1291_; lean_object* v_initHeartbeats_1292_; lean_object* v_maxHeartbeats_1293_; lean_object* v_quotContext_1294_; lean_object* v_currMacroScope_1295_; uint8_t v_diag_1296_; lean_object* v_cancelTk_x3f_1297_; uint8_t v_suppressElabErrors_1298_; lean_object* v_inheritedTraceOptions_1299_; lean_object* v_ref_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_fileName_1284_ = lean_ctor_get(v_a_1281_, 0);
v_fileMap_1285_ = lean_ctor_get(v_a_1281_, 1);
v_options_1286_ = lean_ctor_get(v_a_1281_, 2);
v_currRecDepth_1287_ = lean_ctor_get(v_a_1281_, 3);
v_maxRecDepth_1288_ = lean_ctor_get(v_a_1281_, 4);
v_ref_1289_ = lean_ctor_get(v_a_1281_, 5);
v_currNamespace_1290_ = lean_ctor_get(v_a_1281_, 6);
v_openDecls_1291_ = lean_ctor_get(v_a_1281_, 7);
v_initHeartbeats_1292_ = lean_ctor_get(v_a_1281_, 8);
v_maxHeartbeats_1293_ = lean_ctor_get(v_a_1281_, 9);
v_quotContext_1294_ = lean_ctor_get(v_a_1281_, 10);
v_currMacroScope_1295_ = lean_ctor_get(v_a_1281_, 11);
v_diag_1296_ = lean_ctor_get_uint8(v_a_1281_, sizeof(void*)*14);
v_cancelTk_x3f_1297_ = lean_ctor_get(v_a_1281_, 12);
v_suppressElabErrors_1298_ = lean_ctor_get_uint8(v_a_1281_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1299_ = lean_ctor_get(v_a_1281_, 13);
v_ref_1300_ = l_Lean_replaceRef(v_stx_1276_, v_ref_1289_);
lean_inc_ref(v_inheritedTraceOptions_1299_);
lean_inc(v_cancelTk_x3f_1297_);
lean_inc(v_currMacroScope_1295_);
lean_inc(v_quotContext_1294_);
lean_inc(v_maxHeartbeats_1293_);
lean_inc(v_initHeartbeats_1292_);
lean_inc(v_openDecls_1291_);
lean_inc(v_currNamespace_1290_);
lean_inc(v_maxRecDepth_1288_);
lean_inc(v_currRecDepth_1287_);
lean_inc_ref(v_options_1286_);
lean_inc_ref(v_fileMap_1285_);
lean_inc_ref(v_fileName_1284_);
v___x_1301_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1301_, 0, v_fileName_1284_);
lean_ctor_set(v___x_1301_, 1, v_fileMap_1285_);
lean_ctor_set(v___x_1301_, 2, v_options_1286_);
lean_ctor_set(v___x_1301_, 3, v_currRecDepth_1287_);
lean_ctor_set(v___x_1301_, 4, v_maxRecDepth_1288_);
lean_ctor_set(v___x_1301_, 5, v_ref_1300_);
lean_ctor_set(v___x_1301_, 6, v_currNamespace_1290_);
lean_ctor_set(v___x_1301_, 7, v_openDecls_1291_);
lean_ctor_set(v___x_1301_, 8, v_initHeartbeats_1292_);
lean_ctor_set(v___x_1301_, 9, v_maxHeartbeats_1293_);
lean_ctor_set(v___x_1301_, 10, v_quotContext_1294_);
lean_ctor_set(v___x_1301_, 11, v_currMacroScope_1295_);
lean_ctor_set(v___x_1301_, 12, v_cancelTk_x3f_1297_);
lean_ctor_set(v___x_1301_, 13, v_inheritedTraceOptions_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*14, v_diag_1296_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*14 + 1, v_suppressElabErrors_1298_);
lean_inc(v_stx_1276_);
v___x_1302_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_stx_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v___x_1301_, v_a_1282_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref_known(v___x_1301_, 14);
lean_dec(v_stx_1276_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_fst_1307_; lean_object* v___x_1309_; 
v_fst_1307_ = lean_ctor_get(v_a_1303_, 0);
lean_inc(v_fst_1307_);
lean_dec(v_a_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_fst_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_fst_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1327_; 
v_a_1312_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1314_ = v___x_1302_;
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1302_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1312_);
if (v_isShared_1315_ == 0)
{
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1312_);
v___x_1318_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
uint8_t v___y_1320_; uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_Exception_isInterrupt(v_a_1312_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
lean_inc(v_a_1312_);
v___x_1325_ = l_Lean_Exception_isRuntime(v_a_1312_);
v___y_1320_ = v___x_1325_;
goto v___jp_1319_;
}
else
{
v___y_1320_ = v___x_1324_;
goto v___jp_1319_;
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
if (lean_obj_tag(v_a_1312_) == 0)
{
lean_dec_ref_known(v_a_1312_, 2);
lean_dec_ref_known(v___x_1301_, 14);
lean_dec(v_stx_1276_);
return v___x_1318_;
}
else
{
lean_object* v_id_1321_; uint8_t v___x_1322_; 
v_id_1321_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_id_1321_);
lean_dec_ref_known(v_a_1312_, 2);
v___x_1322_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1316_, v_id_1321_);
lean_dec(v_id_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref_known(v___x_1301_, 14);
lean_dec(v_stx_1276_);
return v___x_1318_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v___x_1318_);
v___x_1323_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v___x_1301_, v_a_1282_);
lean_dec_ref_known(v___x_1301_, 14);
return v___x_1323_;
}
}
}
else
{
lean_dec(v_a_1312_);
lean_dec_ref_known(v___x_1301_, 14);
lean_dec(v_stx_1276_);
return v___x_1318_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
return v_res_1336_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1342_ = l_Lean_mkConst(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1343_; lean_object* v_ty_x3f_1344_; 
v___x_1343_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1344_, 0, v___x_1343_);
return v_ty_x3f_1344_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1346_ = l_Lean_MessageData_ofExpr(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_ty_x3f_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_fileName_1367_; lean_object* v_fileMap_1368_; lean_object* v_options_1369_; lean_object* v_currRecDepth_1370_; lean_object* v_maxRecDepth_1371_; lean_object* v_ref_1372_; lean_object* v_currNamespace_1373_; lean_object* v_openDecls_1374_; lean_object* v_initHeartbeats_1375_; lean_object* v_maxHeartbeats_1376_; lean_object* v_quotContext_1377_; lean_object* v_currMacroScope_1378_; uint8_t v_diag_1379_; lean_object* v_cancelTk_x3f_1380_; uint8_t v_suppressElabErrors_1381_; lean_object* v_inheritedTraceOptions_1382_; uint8_t v___x_1383_; lean_object* v_ref_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_ty_x3f_1361_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1362_ = 1;
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_box(v___x_1362_);
v___x_1365_ = lean_box(v___x_1362_);
lean_inc(v_stx_1353_);
v___x_1366_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1366_, 0, v_stx_1353_);
lean_closure_set(v___x_1366_, 1, v_ty_x3f_1361_);
lean_closure_set(v___x_1366_, 2, v___x_1364_);
lean_closure_set(v___x_1366_, 3, v___x_1365_);
lean_closure_set(v___x_1366_, 4, v___x_1363_);
v_fileName_1367_ = lean_ctor_get(v_a_1358_, 0);
v_fileMap_1368_ = lean_ctor_get(v_a_1358_, 1);
v_options_1369_ = lean_ctor_get(v_a_1358_, 2);
v_currRecDepth_1370_ = lean_ctor_get(v_a_1358_, 3);
v_maxRecDepth_1371_ = lean_ctor_get(v_a_1358_, 4);
v_ref_1372_ = lean_ctor_get(v_a_1358_, 5);
v_currNamespace_1373_ = lean_ctor_get(v_a_1358_, 6);
v_openDecls_1374_ = lean_ctor_get(v_a_1358_, 7);
v_initHeartbeats_1375_ = lean_ctor_get(v_a_1358_, 8);
v_maxHeartbeats_1376_ = lean_ctor_get(v_a_1358_, 9);
v_quotContext_1377_ = lean_ctor_get(v_a_1358_, 10);
v_currMacroScope_1378_ = lean_ctor_get(v_a_1358_, 11);
v_diag_1379_ = lean_ctor_get_uint8(v_a_1358_, sizeof(void*)*14);
v_cancelTk_x3f_1380_ = lean_ctor_get(v_a_1358_, 12);
v_suppressElabErrors_1381_ = lean_ctor_get_uint8(v_a_1358_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1382_ = lean_ctor_get(v_a_1358_, 13);
v___x_1383_ = 1;
v_ref_1384_ = l_Lean_replaceRef(v_stx_1353_, v_ref_1372_);
lean_dec(v_stx_1353_);
lean_inc_ref(v_inheritedTraceOptions_1382_);
lean_inc(v_cancelTk_x3f_1380_);
lean_inc(v_currMacroScope_1378_);
lean_inc(v_quotContext_1377_);
lean_inc(v_maxHeartbeats_1376_);
lean_inc(v_initHeartbeats_1375_);
lean_inc(v_openDecls_1374_);
lean_inc(v_currNamespace_1373_);
lean_inc(v_maxRecDepth_1371_);
lean_inc(v_currRecDepth_1370_);
lean_inc_ref(v_options_1369_);
lean_inc_ref(v_fileMap_1368_);
lean_inc_ref(v_fileName_1367_);
v___x_1385_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1385_, 0, v_fileName_1367_);
lean_ctor_set(v___x_1385_, 1, v_fileMap_1368_);
lean_ctor_set(v___x_1385_, 2, v_options_1369_);
lean_ctor_set(v___x_1385_, 3, v_currRecDepth_1370_);
lean_ctor_set(v___x_1385_, 4, v_maxRecDepth_1371_);
lean_ctor_set(v___x_1385_, 5, v_ref_1384_);
lean_ctor_set(v___x_1385_, 6, v_currNamespace_1373_);
lean_ctor_set(v___x_1385_, 7, v_openDecls_1374_);
lean_ctor_set(v___x_1385_, 8, v_initHeartbeats_1375_);
lean_ctor_set(v___x_1385_, 9, v_maxHeartbeats_1376_);
lean_ctor_set(v___x_1385_, 10, v_quotContext_1377_);
lean_ctor_set(v___x_1385_, 11, v_currMacroScope_1378_);
lean_ctor_set(v___x_1385_, 12, v_cancelTk_x3f_1380_);
lean_ctor_set(v___x_1385_, 13, v_inheritedTraceOptions_1382_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*14, v_diag_1379_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*14 + 1, v_suppressElabErrors_1381_);
v___x_1386_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1366_, v___x_1383_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v___x_1385_, v_a_1359_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v___x_1484_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1387_, v_a_1357_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
v___x_1484_ = l_Lean_Expr_hasSorry(v_a_1389_);
if (v___x_1484_ == 0)
{
v___y_1429_ = v_a_1354_;
v___y_1430_ = v_a_1355_;
v___y_1431_ = v_a_1356_;
v___y_1432_ = v_a_1357_;
v___y_1433_ = v___x_1385_;
v___y_1434_ = v_a_1359_;
goto v___jp_1428_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Lean_Expr_hasSyntheticSorry(v_a_1389_);
if (v___x_1485_ == 0)
{
v___y_1466_ = v_a_1354_;
v___y_1467_ = v_a_1355_;
v___y_1468_ = v_a_1356_;
v___y_1469_ = v_a_1357_;
v___y_1470_ = v___x_1385_;
v___y_1471_ = v_a_1359_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1389_);
lean_dec_ref_known(v___x_1385_, 14);
v___x_1486_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
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
v___jp_1390_:
{
if (v___y_1400_ == 0)
{
if (lean_obj_tag(v___y_1394_) == 0)
{
lean_dec_ref_known(v___y_1394_, 2);
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1389_);
return v___y_1396_;
}
else
{
lean_object* v_id_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1414_; 
v_id_1401_ = lean_ctor_get(v___y_1394_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___y_1394_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___y_1394_, 1);
lean_dec(v_unused_1415_);
v___x_1403_ = v___y_1394_;
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_id_1401_);
lean_dec(v___y_1394_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1392_, v_id_1401_);
lean_dec(v_id_1401_);
if (v___x_1405_ == 0)
{
lean_del_object(v___x_1403_);
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1389_);
return v___y_1396_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v___y_1396_);
v___x_1406_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1407_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1408_ = l_Lean_indentExpr(v_a_1389_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 7);
lean_ctor_set(v___x_1403_, 1, v___x_1408_);
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1410_ = v___x_1403_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1406_);
v___x_1412_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1411_, v___y_1393_, v___y_1399_, v___y_1398_, v___y_1397_, v___y_1391_, v___y_1395_);
lean_dec_ref(v___y_1391_);
return v___x_1412_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1389_);
return v___y_1396_;
}
}
v___jp_1416_:
{
lean_object* v___x_1423_; 
lean_inc(v_a_1389_);
v___x_1423_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1389_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_dec_ref(v___y_1421_);
lean_dec(v_a_1389_);
return v___x_1423_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
v___x_1425_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1426_ = l_Lean_Exception_isInterrupt(v_a_1424_);
if (v___x_1426_ == 0)
{
uint8_t v___x_1427_; 
lean_inc(v_a_1424_);
v___x_1427_ = l_Lean_Exception_isRuntime(v_a_1424_);
v___y_1391_ = v___y_1421_;
v___y_1392_ = v___x_1425_;
v___y_1393_ = v___y_1417_;
v___y_1394_ = v_a_1424_;
v___y_1395_ = v___y_1422_;
v___y_1396_ = v___x_1423_;
v___y_1397_ = v___y_1420_;
v___y_1398_ = v___y_1419_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___x_1427_;
goto v___jp_1390_;
}
else
{
v___y_1391_ = v___y_1421_;
v___y_1392_ = v___x_1425_;
v___y_1393_ = v___y_1417_;
v___y_1394_ = v_a_1424_;
v___y_1395_ = v___y_1422_;
v___y_1396_ = v___x_1423_;
v___y_1397_ = v___y_1420_;
v___y_1398_ = v___y_1419_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___x_1426_;
goto v___jp_1390_;
}
}
}
v___jp_1428_:
{
lean_object* v___x_1435_; 
lean_inc(v_a_1389_);
v___x_1435_ = l_Lean_Meta_getMVars(v_a_1389_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1436_, v___x_1363_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v_a_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_unbox(v_a_1438_);
lean_dec(v_a_1438_);
if (v___x_1439_ == 0)
{
v___y_1417_ = v___y_1429_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___y_1432_;
v___y_1421_ = v___y_1433_;
v___y_1422_ = v___y_1434_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1440_; lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1389_);
v___x_1440_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1389_);
v_a_1449_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1437_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1437_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1389_);
v_a_1457_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1435_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1435_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v___x_1472_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1473_ = l_Lean_indentExpr(v_a_1389_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1474_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec_ref(v___y_1470_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref_known(v___x_1385_, 14);
v_a_1495_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1386_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1386_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_fileName_1520_; lean_object* v_fileMap_1521_; lean_object* v_options_1522_; lean_object* v_currRecDepth_1523_; lean_object* v_maxRecDepth_1524_; lean_object* v_ref_1525_; lean_object* v_currNamespace_1526_; lean_object* v_openDecls_1527_; lean_object* v_initHeartbeats_1528_; lean_object* v_maxHeartbeats_1529_; lean_object* v_quotContext_1530_; lean_object* v_currMacroScope_1531_; uint8_t v_diag_1532_; lean_object* v_cancelTk_x3f_1533_; uint8_t v_suppressElabErrors_1534_; lean_object* v_inheritedTraceOptions_1535_; lean_object* v_ref_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_fileName_1520_ = lean_ctor_get(v_a_1517_, 0);
v_fileMap_1521_ = lean_ctor_get(v_a_1517_, 1);
v_options_1522_ = lean_ctor_get(v_a_1517_, 2);
v_currRecDepth_1523_ = lean_ctor_get(v_a_1517_, 3);
v_maxRecDepth_1524_ = lean_ctor_get(v_a_1517_, 4);
v_ref_1525_ = lean_ctor_get(v_a_1517_, 5);
v_currNamespace_1526_ = lean_ctor_get(v_a_1517_, 6);
v_openDecls_1527_ = lean_ctor_get(v_a_1517_, 7);
v_initHeartbeats_1528_ = lean_ctor_get(v_a_1517_, 8);
v_maxHeartbeats_1529_ = lean_ctor_get(v_a_1517_, 9);
v_quotContext_1530_ = lean_ctor_get(v_a_1517_, 10);
v_currMacroScope_1531_ = lean_ctor_get(v_a_1517_, 11);
v_diag_1532_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*14);
v_cancelTk_x3f_1533_ = lean_ctor_get(v_a_1517_, 12);
v_suppressElabErrors_1534_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1535_ = lean_ctor_get(v_a_1517_, 13);
v_ref_1536_ = l_Lean_replaceRef(v_stx_1512_, v_ref_1525_);
lean_inc_ref(v_inheritedTraceOptions_1535_);
lean_inc(v_cancelTk_x3f_1533_);
lean_inc(v_currMacroScope_1531_);
lean_inc(v_quotContext_1530_);
lean_inc(v_maxHeartbeats_1529_);
lean_inc(v_initHeartbeats_1528_);
lean_inc(v_openDecls_1527_);
lean_inc(v_currNamespace_1526_);
lean_inc(v_maxRecDepth_1524_);
lean_inc(v_currRecDepth_1523_);
lean_inc_ref(v_options_1522_);
lean_inc_ref(v_fileMap_1521_);
lean_inc_ref(v_fileName_1520_);
v___x_1537_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1537_, 0, v_fileName_1520_);
lean_ctor_set(v___x_1537_, 1, v_fileMap_1521_);
lean_ctor_set(v___x_1537_, 2, v_options_1522_);
lean_ctor_set(v___x_1537_, 3, v_currRecDepth_1523_);
lean_ctor_set(v___x_1537_, 4, v_maxRecDepth_1524_);
lean_ctor_set(v___x_1537_, 5, v_ref_1536_);
lean_ctor_set(v___x_1537_, 6, v_currNamespace_1526_);
lean_ctor_set(v___x_1537_, 7, v_openDecls_1527_);
lean_ctor_set(v___x_1537_, 8, v_initHeartbeats_1528_);
lean_ctor_set(v___x_1537_, 9, v_maxHeartbeats_1529_);
lean_ctor_set(v___x_1537_, 10, v_quotContext_1530_);
lean_ctor_set(v___x_1537_, 11, v_currMacroScope_1531_);
lean_ctor_set(v___x_1537_, 12, v_cancelTk_x3f_1533_);
lean_ctor_set(v___x_1537_, 13, v_inheritedTraceOptions_1535_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*14, v_diag_1532_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*14 + 1, v_suppressElabErrors_1534_);
lean_inc(v_stx_1512_);
v___x_1538_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v___x_1537_, v_a_1518_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref_known(v___x_1537_, 14);
lean_dec(v_stx_1512_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_fst_1543_; lean_object* v___x_1545_; 
v_fst_1543_ = lean_ctor_get(v_a_1539_, 0);
lean_inc(v_fst_1543_);
lean_dec(v_a_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_fst_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_fst_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1563_; 
v_a_1548_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1550_ = v___x_1538_;
v_isShared_1551_ = v_isSharedCheck_1563_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1538_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1563_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1548_);
if (v_isShared_1551_ == 0)
{
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1548_);
v___x_1554_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
uint8_t v___y_1556_; uint8_t v___x_1560_; 
v___x_1560_ = l_Lean_Exception_isInterrupt(v_a_1548_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
lean_inc(v_a_1548_);
v___x_1561_ = l_Lean_Exception_isRuntime(v_a_1548_);
v___y_1556_ = v___x_1561_;
goto v___jp_1555_;
}
else
{
v___y_1556_ = v___x_1560_;
goto v___jp_1555_;
}
v___jp_1555_:
{
if (v___y_1556_ == 0)
{
if (lean_obj_tag(v_a_1548_) == 0)
{
lean_dec_ref_known(v_a_1548_, 2);
lean_dec_ref_known(v___x_1537_, 14);
lean_dec(v_stx_1512_);
return v___x_1554_;
}
else
{
lean_object* v_id_1557_; uint8_t v___x_1558_; 
v_id_1557_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_id_1557_);
lean_dec_ref_known(v_a_1548_, 2);
v___x_1558_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1552_, v_id_1557_);
lean_dec(v_id_1557_);
if (v___x_1558_ == 0)
{
lean_dec_ref_known(v___x_1537_, 14);
lean_dec(v_stx_1512_);
return v___x_1554_;
}
else
{
lean_object* v___x_1559_; 
lean_dec_ref(v___x_1554_);
v___x_1559_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v___x_1537_, v_a_1518_);
lean_dec_ref_known(v___x_1537_, 14);
return v___x_1559_;
}
}
}
else
{
lean_dec(v_a_1548_);
lean_dec_ref_known(v___x_1537_, 14);
lean_dec(v_stx_1512_);
return v___x_1554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1680_, lean_object* v_item_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_item_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1700_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1681_, v___x_1699_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1700_) == 0)
{
uint8_t v___x_1701_; 
lean_dec_ref_known(v___x_1700_, 1);
v___x_1701_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1681_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1702_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1681_);
lean_inc_ref(v_item_1681_);
v___x_1703_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1681_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1705_ = lean_string_dec_lt(v___x_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1707_ = lean_string_dec_lt(v___x_1702_, v___x_1706_);
if (v___x_1707_ == 0)
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_string_dec_eq(v___x_1702_, v___x_1706_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1710_ = lean_string_dec_eq(v___x_1702_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1712_ = lean_string_dec_eq(v___x_1702_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1714_ = lean_string_dec_eq(v___x_1702_, v___x_1713_);
lean_dec_ref(v___x_1702_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1716_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1715_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1716_) == 0)
{
uint8_t v___x_1717_; 
lean_dec_ref_known(v___x_1716_, 1);
v___x_1717_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1717_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1718_; 
lean_dec_ref(v___x_1703_);
v___x_1718_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1746_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1746_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1746_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_timeout_1723_; uint8_t v_binaryProofs_1724_; uint8_t v_acNf_1725_; uint8_t v_andFlattening_1726_; uint8_t v_embeddedConstraintSubst_1727_; uint8_t v_structures_1728_; uint8_t v_fixedInt_1729_; uint8_t v_enums_1730_; uint8_t v_graphviz_1731_; lean_object* v_maxSteps_1732_; uint8_t v_shortCircuit_1733_; uint8_t v_solverMode_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1745_; 
v_timeout_1723_ = lean_ctor_get(v_config_1680_, 0);
v_binaryProofs_1724_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1725_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1726_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1727_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_1728_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_1729_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1730_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1731_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_1732_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_1733_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_1734_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1736_ = v_config_1680_;
v_isShared_1737_ = v_isSharedCheck_1745_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_maxSteps_1732_);
lean_inc(v_timeout_1723_);
lean_dec(v_config_1680_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1745_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_timeout_1723_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_maxSteps_1732_);
v___x_1739_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
uint8_t v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_unbox(v_a_1719_);
lean_dec(v_a_1719_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2, v___x_1740_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 1, v_binaryProofs_1724_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 2, v_acNf_1725_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 3, v_andFlattening_1726_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1727_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 5, v_structures_1728_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 6, v_fixedInt_1729_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 7, v_enums_1730_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 8, v_graphviz_1731_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 9, v_shortCircuit_1733_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*2 + 10, v_solverMode_1734_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1739_);
v___x_1742_ = v___x_1721_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1739_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_config_1680_);
v_a_1747_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1718_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1718_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1755_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1716_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1716_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
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
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec_ref(v___x_1702_);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1764_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1763_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1764_) == 0)
{
uint8_t v___x_1765_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1765_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1766_; 
lean_dec_ref(v___x_1703_);
lean_inc_ref(v_item_1681_);
v___x_1766_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_value_1767_; lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1766_, 1);
v_value_1767_ = lean_ctor_get(v_item_1681_, 2);
lean_inc(v_value_1767_);
lean_dec_ref(v_item_1681_);
v___x_1768_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1767_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1796_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1796_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint8_t v_trimProofs_1773_; uint8_t v_binaryProofs_1774_; uint8_t v_acNf_1775_; uint8_t v_andFlattening_1776_; uint8_t v_embeddedConstraintSubst_1777_; uint8_t v_structures_1778_; uint8_t v_fixedInt_1779_; uint8_t v_enums_1780_; uint8_t v_graphviz_1781_; lean_object* v_maxSteps_1782_; uint8_t v_shortCircuit_1783_; uint8_t v_solverMode_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1794_; 
v_trimProofs_1773_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_1774_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1775_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1776_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1777_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_1778_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_1779_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1780_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1781_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_1782_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_1783_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_1784_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_config_1680_, 0);
lean_dec(v_unused_1795_);
v___x_1786_ = v_config_1680_;
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_maxSteps_1782_);
lean_dec(v_config_1680_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_a_1769_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1769_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_maxSteps_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2, v_trimProofs_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 1, v_binaryProofs_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 2, v_acNf_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 3, v_andFlattening_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 5, v_structures_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 6, v_fixedInt_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 7, v_enums_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 8, v_graphviz_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 9, v_shortCircuit_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*2 + 10, v_solverMode_1784_);
v___x_1789_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1789_);
v___x_1791_ = v___x_1771_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
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
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_config_1680_);
v_a_1797_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1768_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1768_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1805_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1766_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1766_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1813_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1764_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1764_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
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
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v___x_1702_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1822_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1821_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1822_) == 0)
{
uint8_t v___x_1823_; 
lean_dec_ref_known(v___x_1822_, 1);
v___x_1823_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1823_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1824_; 
lean_dec_ref(v___x_1703_);
v___x_1824_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1852_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1852_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1852_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_timeout_1829_; uint8_t v_trimProofs_1830_; uint8_t v_binaryProofs_1831_; uint8_t v_acNf_1832_; uint8_t v_andFlattening_1833_; uint8_t v_embeddedConstraintSubst_1834_; uint8_t v_fixedInt_1835_; uint8_t v_enums_1836_; uint8_t v_graphviz_1837_; lean_object* v_maxSteps_1838_; uint8_t v_shortCircuit_1839_; uint8_t v_solverMode_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1851_; 
v_timeout_1829_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_1830_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_1831_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1832_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1833_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1834_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_fixedInt_1835_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1836_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1837_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_1838_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_1839_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_1840_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1842_ = v_config_1680_;
v_isShared_1843_ = v_isSharedCheck_1851_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_maxSteps_1838_);
lean_inc(v_timeout_1829_);
lean_dec(v_config_1680_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1851_;
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
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_timeout_1829_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_maxSteps_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*2, v_trimProofs_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*2 + 1, v_binaryProofs_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*2 + 2, v_acNf_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*2 + 3, v_andFlattening_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1834_);
v___x_1845_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
uint8_t v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_unbox(v_a_1825_);
lean_dec(v_a_1825_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 5, v___x_1846_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 6, v_fixedInt_1835_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 7, v_enums_1836_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 8, v_graphviz_1837_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 9, v_shortCircuit_1839_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*2 + 10, v_solverMode_1840_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1845_);
v___x_1848_ = v___x_1827_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1845_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_config_1680_);
v_a_1853_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1824_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1824_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1861_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1822_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1822_);
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
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v___x_1702_);
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1870_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1869_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1870_) == 0)
{
uint8_t v___x_1871_; 
lean_dec_ref_known(v___x_1870_, 1);
v___x_1871_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1871_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1703_);
lean_inc_ref(v_item_1681_);
v___x_1872_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_value_1873_; lean_object* v___x_1874_; 
lean_dec_ref_known(v___x_1872_, 1);
v_value_1873_ = lean_ctor_get(v_item_1681_, 2);
lean_inc(v_value_1873_);
lean_dec_ref(v_item_1681_);
v___x_1874_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1873_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1902_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1902_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1902_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_timeout_1879_; uint8_t v_trimProofs_1880_; uint8_t v_binaryProofs_1881_; uint8_t v_acNf_1882_; uint8_t v_andFlattening_1883_; uint8_t v_embeddedConstraintSubst_1884_; uint8_t v_structures_1885_; uint8_t v_fixedInt_1886_; uint8_t v_enums_1887_; uint8_t v_graphviz_1888_; lean_object* v_maxSteps_1889_; uint8_t v_shortCircuit_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1901_; 
v_timeout_1879_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_1880_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_1881_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1882_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1883_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1884_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_1885_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_1886_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1887_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1888_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_1889_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_1890_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1892_ = v_config_1680_;
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_maxSteps_1889_);
lean_inc(v_timeout_1879_);
lean_dec(v_config_1680_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_timeout_1879_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_maxSteps_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2, v_trimProofs_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 1, v_binaryProofs_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 2, v_acNf_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 3, v_andFlattening_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 5, v_structures_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 6, v_fixedInt_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 7, v_enums_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 8, v_graphviz_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*2 + 9, v_shortCircuit_1890_);
v___x_1895_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
uint8_t v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_unbox(v_a_1875_);
lean_dec(v_a_1875_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*2 + 10, v___x_1896_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1895_);
v___x_1898_ = v___x_1877_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1895_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_config_1680_);
v_a_1903_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1874_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1874_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1911_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1872_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1872_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1919_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1870_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1870_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_string_dec_eq(v___x_1702_, v___x_1704_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1929_ = lean_string_dec_eq(v___x_1702_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1931_ = lean_string_dec_eq(v___x_1702_, v___x_1930_);
lean_dec_ref(v___x_1702_);
if (v___x_1931_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1933_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1932_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1933_) == 0)
{
uint8_t v___x_1934_; 
lean_dec_ref_known(v___x_1933_, 1);
v___x_1934_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1934_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1935_; 
lean_dec_ref(v___x_1703_);
v___x_1935_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1963_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1963_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1963_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_timeout_1940_; uint8_t v_trimProofs_1941_; uint8_t v_binaryProofs_1942_; uint8_t v_acNf_1943_; uint8_t v_andFlattening_1944_; uint8_t v_embeddedConstraintSubst_1945_; uint8_t v_structures_1946_; uint8_t v_fixedInt_1947_; uint8_t v_enums_1948_; uint8_t v_graphviz_1949_; lean_object* v_maxSteps_1950_; uint8_t v_solverMode_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1962_; 
v_timeout_1940_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_1941_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_1942_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1943_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1944_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1945_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_1946_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_1947_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1948_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1949_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_1950_ = lean_ctor_get(v_config_1680_, 1);
v_solverMode_1951_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1953_ = v_config_1680_;
v_isShared_1954_ = v_isSharedCheck_1962_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_maxSteps_1950_);
lean_inc(v_timeout_1940_);
lean_dec(v_config_1680_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1962_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_timeout_1940_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_maxSteps_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2, v_trimProofs_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 1, v_binaryProofs_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 2, v_acNf_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 3, v_andFlattening_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 5, v_structures_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 6, v_fixedInt_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 7, v_enums_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*2 + 8, v_graphviz_1949_);
v___x_1956_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
uint8_t v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*2 + 9, v___x_1957_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*2 + 10, v_solverMode_1951_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1956_);
v___x_1959_ = v___x_1938_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1956_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_config_1680_);
v_a_1964_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1935_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1935_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_1972_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1933_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1933_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v___x_1702_);
v___x_1980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_1981_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_1980_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1981_) == 0)
{
uint8_t v___x_1982_; 
lean_dec_ref_known(v___x_1981_, 1);
v___x_1982_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1983_; 
lean_dec_ref(v___x_1703_);
lean_inc_ref(v_item_1681_);
v___x_1983_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_value_1984_; lean_object* v___x_1985_; 
lean_dec_ref_known(v___x_1983_, 1);
v_value_1984_ = lean_ctor_get(v_item_1681_, 2);
lean_inc(v_value_1984_);
lean_dec_ref(v_item_1681_);
v___x_1985_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1984_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2013_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2013_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2013_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_timeout_1990_; uint8_t v_trimProofs_1991_; uint8_t v_binaryProofs_1992_; uint8_t v_acNf_1993_; uint8_t v_andFlattening_1994_; uint8_t v_embeddedConstraintSubst_1995_; uint8_t v_structures_1996_; uint8_t v_fixedInt_1997_; uint8_t v_enums_1998_; uint8_t v_graphviz_1999_; uint8_t v_shortCircuit_2000_; uint8_t v_solverMode_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
v_timeout_1990_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_1991_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_1992_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_1993_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_1994_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1995_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_1996_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_1997_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_1998_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_1999_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_shortCircuit_2000_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2001_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_config_1680_, 1);
lean_dec(v_unused_2012_);
v___x_2003_ = v_config_1680_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_timeout_1990_);
lean_dec(v_config_1680_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_a_1986_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_timeout_1990_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_a_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2, v_trimProofs_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 1, v_binaryProofs_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 2, v_acNf_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 3, v_andFlattening_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 5, v_structures_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 6, v_fixedInt_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 7, v_enums_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 8, v_graphviz_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 9, v_shortCircuit_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 10, v_solverMode_2001_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_2006_);
v___x_2008_ = v___x_1988_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v_config_1680_);
v_a_2014_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1985_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1985_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2022_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1983_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1983_);
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
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2030_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1981_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1981_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
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
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v___x_1702_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_2039_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2038_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2039_) == 0)
{
uint8_t v___x_2040_; 
lean_dec_ref_known(v___x_2039_, 1);
v___x_2040_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2041_; 
lean_dec_ref(v___x_1703_);
v___x_2041_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2069_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2069_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2069_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_timeout_2046_; uint8_t v_trimProofs_2047_; uint8_t v_binaryProofs_2048_; uint8_t v_acNf_2049_; uint8_t v_andFlattening_2050_; uint8_t v_embeddedConstraintSubst_2051_; uint8_t v_structures_2052_; uint8_t v_fixedInt_2053_; uint8_t v_enums_2054_; lean_object* v_maxSteps_2055_; uint8_t v_shortCircuit_2056_; uint8_t v_solverMode_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2068_; 
v_timeout_2046_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2047_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2048_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_2049_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_2050_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2051_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2052_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2053_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_2054_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_maxSteps_2055_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2056_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2057_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2059_ = v_config_1680_;
v_isShared_2060_ = v_isSharedCheck_2068_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_maxSteps_2055_);
lean_inc(v_timeout_2046_);
lean_dec(v_config_1680_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2068_;
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
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_timeout_2046_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_maxSteps_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2, v_trimProofs_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 1, v_binaryProofs_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 2, v_acNf_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 3, v_andFlattening_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 5, v_structures_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 6, v_fixedInt_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*2 + 7, v_enums_2054_);
v___x_2062_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
uint8_t v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_unbox(v_a_2042_);
lean_dec(v_a_2042_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*2 + 8, v___x_2063_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*2 + 9, v_shortCircuit_2056_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*2 + 10, v_solverMode_2057_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2062_);
v___x_2065_ = v___x_2044_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2062_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_config_1680_);
v_a_2070_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2041_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2041_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2078_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2039_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2039_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
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
}
}
else
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2087_ = lean_string_dec_lt(v___x_1702_, v___x_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_string_dec_eq(v___x_1702_, v___x_2086_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2090_ = lean_string_dec_eq(v___x_1702_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2092_ = lean_string_dec_eq(v___x_1702_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2094_ = lean_string_dec_eq(v___x_1702_, v___x_2093_);
lean_dec_ref(v___x_1702_);
if (v___x_2094_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2096_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2095_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2096_) == 0)
{
uint8_t v___x_2097_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2097_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2097_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v___x_1703_);
v___x_2098_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2126_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2126_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2126_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_timeout_2103_; uint8_t v_trimProofs_2104_; uint8_t v_binaryProofs_2105_; uint8_t v_acNf_2106_; uint8_t v_andFlattening_2107_; uint8_t v_embeddedConstraintSubst_2108_; uint8_t v_structures_2109_; uint8_t v_enums_2110_; uint8_t v_graphviz_2111_; lean_object* v_maxSteps_2112_; uint8_t v_shortCircuit_2113_; uint8_t v_solverMode_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
v_timeout_2103_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2104_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2105_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_2106_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_2107_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2108_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2109_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_enums_2110_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_2111_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2112_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2113_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2114_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2116_ = v_config_1680_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_maxSteps_2112_);
lean_inc(v_timeout_2103_);
lean_dec(v_config_1680_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_timeout_2103_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_maxSteps_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2, v_trimProofs_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2 + 1, v_binaryProofs_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2 + 2, v_acNf_2106_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2 + 3, v_andFlattening_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*2 + 5, v_structures_2109_);
v___x_2119_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
uint8_t v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_unbox(v_a_2099_);
lean_dec(v_a_2099_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*2 + 6, v___x_2120_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*2 + 7, v_enums_2110_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*2 + 8, v_graphviz_2111_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*2 + 9, v_shortCircuit_2113_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*2 + 10, v_solverMode_2114_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2119_);
v___x_2122_ = v___x_2101_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2119_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_config_1680_);
v_a_2127_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2098_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2098_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2135_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2096_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2096_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v___x_1702_);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2144_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2143_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2144_) == 0)
{
uint8_t v___x_2145_; 
lean_dec_ref_known(v___x_2144_, 1);
v___x_2145_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2145_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2146_; 
lean_dec_ref(v___x_1703_);
v___x_2146_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2174_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2174_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2174_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_timeout_2151_; uint8_t v_trimProofs_2152_; uint8_t v_binaryProofs_2153_; uint8_t v_acNf_2154_; uint8_t v_andFlattening_2155_; uint8_t v_embeddedConstraintSubst_2156_; uint8_t v_structures_2157_; uint8_t v_fixedInt_2158_; uint8_t v_graphviz_2159_; lean_object* v_maxSteps_2160_; uint8_t v_shortCircuit_2161_; uint8_t v_solverMode_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2173_; 
v_timeout_2151_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2152_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2153_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_2154_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_2155_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2156_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2157_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2158_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_graphviz_2159_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2160_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2161_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2162_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2164_ = v_config_1680_;
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_maxSteps_2160_);
lean_inc(v_timeout_2151_);
lean_dec(v_config_1680_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2173_;
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
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_timeout_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_maxSteps_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2, v_trimProofs_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 1, v_binaryProofs_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 2, v_acNf_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 3, v_andFlattening_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 5, v_structures_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*2 + 6, v_fixedInt_2158_);
v___x_2167_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
uint8_t v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_unbox(v_a_2147_);
lean_dec(v_a_2147_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*2 + 7, v___x_2168_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*2 + 8, v_graphviz_2159_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*2 + 9, v_shortCircuit_2161_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*2 + 10, v_solverMode_2162_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2167_);
v___x_2170_ = v___x_2149_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
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
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v_config_1680_);
v_a_2175_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2146_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2146_);
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
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2183_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2144_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2144_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v___x_1702_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2192_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2191_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2192_) == 0)
{
uint8_t v___x_2193_; 
lean_dec_ref_known(v___x_2192_, 1);
v___x_2193_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v___x_1703_);
v___x_2194_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2222_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2222_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2222_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_timeout_2199_; uint8_t v_trimProofs_2200_; uint8_t v_binaryProofs_2201_; uint8_t v_acNf_2202_; uint8_t v_andFlattening_2203_; uint8_t v_structures_2204_; uint8_t v_fixedInt_2205_; uint8_t v_enums_2206_; uint8_t v_graphviz_2207_; lean_object* v_maxSteps_2208_; uint8_t v_shortCircuit_2209_; uint8_t v_solverMode_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2221_; 
v_timeout_2199_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2200_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2201_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_2202_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_2203_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_structures_2204_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2205_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_2206_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_2207_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2208_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2209_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2210_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2212_ = v_config_1680_;
v_isShared_2213_ = v_isSharedCheck_2221_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_maxSteps_2208_);
lean_inc(v_timeout_2199_);
lean_dec(v_config_1680_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2221_;
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
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_timeout_2199_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_maxSteps_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*2, v_trimProofs_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*2 + 1, v_binaryProofs_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*2 + 2, v_acNf_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*2 + 3, v_andFlattening_2203_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
uint8_t v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_unbox(v_a_2195_);
lean_dec(v_a_2195_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 4, v___x_2216_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 5, v_structures_2204_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 6, v_fixedInt_2205_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 7, v_enums_2206_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 8, v_graphviz_2207_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 9, v_shortCircuit_2209_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2 + 10, v_solverMode_2210_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2215_);
v___x_2218_ = v___x_2197_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2215_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_config_1680_);
v_a_2223_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2194_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2194_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2231_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2192_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2192_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
uint8_t v___x_2239_; 
lean_dec_ref(v___x_1702_);
lean_dec_ref(v_config_1680_);
v___x_2239_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_item_1681_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v_value_2240_; lean_object* v___x_2241_; 
lean_dec_ref(v___x_1703_);
v_value_2240_ = lean_ctor_get(v_item_1681_, 2);
lean_inc(v_value_2240_);
lean_dec_ref(v_item_1681_);
v___x_2241_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2240_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_2241_;
}
}
}
else
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2243_ = lean_string_dec_eq(v___x_1702_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2245_ = lean_string_dec_eq(v___x_1702_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2247_ = lean_string_dec_eq(v___x_1702_, v___x_2246_);
lean_dec_ref(v___x_1702_);
if (v___x_2247_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2249_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2248_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2249_) == 0)
{
uint8_t v___x_2250_; 
lean_dec_ref_known(v___x_2249_, 1);
v___x_2250_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2251_; 
lean_dec_ref(v___x_1703_);
v___x_2251_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2279_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2279_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2279_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_timeout_2256_; uint8_t v_trimProofs_2257_; uint8_t v_acNf_2258_; uint8_t v_andFlattening_2259_; uint8_t v_embeddedConstraintSubst_2260_; uint8_t v_structures_2261_; uint8_t v_fixedInt_2262_; uint8_t v_enums_2263_; uint8_t v_graphviz_2264_; lean_object* v_maxSteps_2265_; uint8_t v_shortCircuit_2266_; uint8_t v_solverMode_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2278_; 
v_timeout_2256_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2257_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_acNf_2258_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_andFlattening_2259_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2260_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2261_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2262_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_2263_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_2264_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2265_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2266_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2267_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2269_ = v_config_1680_;
v_isShared_2270_ = v_isSharedCheck_2278_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_maxSteps_2265_);
lean_inc(v_timeout_2256_);
lean_dec(v_config_1680_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2278_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_timeout_2256_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_maxSteps_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, sizeof(void*)*2, v_trimProofs_2257_);
v___x_2272_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
uint8_t v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 1, v___x_2273_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 2, v_acNf_2258_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 3, v_andFlattening_2259_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2260_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 5, v_structures_2261_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 6, v_fixedInt_2262_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 7, v_enums_2263_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 8, v_graphviz_2264_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 9, v_shortCircuit_2266_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2 + 10, v_solverMode_2267_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2272_);
v___x_2275_ = v___x_2254_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2272_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_config_1680_);
v_a_2280_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2251_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2251_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2288_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2249_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2249_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v___x_1702_);
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2297_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2296_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2297_) == 0)
{
uint8_t v___x_2298_; 
lean_dec_ref_known(v___x_2297_, 1);
v___x_2298_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2298_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2299_; 
lean_dec_ref(v___x_1703_);
v___x_2299_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2327_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2327_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2327_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_timeout_2304_; uint8_t v_trimProofs_2305_; uint8_t v_binaryProofs_2306_; uint8_t v_acNf_2307_; uint8_t v_embeddedConstraintSubst_2308_; uint8_t v_structures_2309_; uint8_t v_fixedInt_2310_; uint8_t v_enums_2311_; uint8_t v_graphviz_2312_; lean_object* v_maxSteps_2313_; uint8_t v_shortCircuit_2314_; uint8_t v_solverMode_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2326_; 
v_timeout_2304_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2305_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2306_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_acNf_2307_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 2);
v_embeddedConstraintSubst_2308_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2309_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2310_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_2311_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_2312_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2313_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2314_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2315_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2317_ = v_config_1680_;
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_maxSteps_2313_);
lean_inc(v_timeout_2304_);
lean_dec(v_config_1680_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2326_;
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
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_timeout_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_maxSteps_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*2, v_trimProofs_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*2 + 1, v_binaryProofs_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*2 + 2, v_acNf_2307_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
uint8_t v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_unbox(v_a_2300_);
lean_dec(v_a_2300_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 3, v___x_2321_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2308_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 5, v_structures_2309_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 6, v_fixedInt_2310_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 7, v_enums_2311_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 8, v_graphviz_2312_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 9, v_shortCircuit_2314_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 10, v_solverMode_2315_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2320_);
v___x_2323_ = v___x_2302_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2320_);
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
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_config_1680_);
v_a_2328_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2299_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2299_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2336_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2297_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2297_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v___x_1702_);
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2345_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1681_, v___x_2344_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2345_) == 0)
{
uint8_t v___x_2346_; 
lean_dec_ref_known(v___x_2345_, 1);
v___x_2346_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1703_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_item_1690_ = v___x_1703_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_2347_; 
lean_dec_ref(v___x_1703_);
v___x_2347_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2375_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2375_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2375_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_timeout_2352_; uint8_t v_trimProofs_2353_; uint8_t v_binaryProofs_2354_; uint8_t v_andFlattening_2355_; uint8_t v_embeddedConstraintSubst_2356_; uint8_t v_structures_2357_; uint8_t v_fixedInt_2358_; uint8_t v_enums_2359_; uint8_t v_graphviz_2360_; lean_object* v_maxSteps_2361_; uint8_t v_shortCircuit_2362_; uint8_t v_solverMode_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2374_; 
v_timeout_2352_ = lean_ctor_get(v_config_1680_, 0);
v_trimProofs_2353_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2);
v_binaryProofs_2354_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 1);
v_andFlattening_2355_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2356_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 4);
v_structures_2357_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 5);
v_fixedInt_2358_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 6);
v_enums_2359_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 7);
v_graphviz_2360_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 8);
v_maxSteps_2361_ = lean_ctor_get(v_config_1680_, 1);
v_shortCircuit_2362_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 9);
v_solverMode_2363_ = lean_ctor_get_uint8(v_config_1680_, sizeof(void*)*2 + 10);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_config_1680_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2365_ = v_config_1680_;
v_isShared_2366_ = v_isSharedCheck_2374_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_maxSteps_2361_);
lean_inc(v_timeout_2352_);
lean_dec(v_config_1680_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2374_;
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
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_timeout_2352_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_maxSteps_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*2, v_trimProofs_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*2 + 1, v_binaryProofs_2354_);
v___x_2368_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
uint8_t v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_unbox(v_a_2348_);
lean_dec(v_a_2348_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 2, v___x_2369_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 3, v_andFlattening_2355_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2356_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 5, v_structures_2357_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 6, v_fixedInt_2358_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 7, v_enums_2359_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 8, v_graphviz_2360_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 9, v_shortCircuit_2362_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2 + 10, v_solverMode_2363_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2368_);
v___x_2371_ = v___x_2350_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2368_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_config_1680_);
v_a_2376_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2347_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2347_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2384_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2345_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2345_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_config_1680_);
v_item_1690_ = v_item_1681_;
v___y_1691_ = v___y_1682_;
v___y_1692_ = v___y_1683_;
v___y_1693_ = v___y_1684_;
v___y_1694_ = v___y_1685_;
v___y_1695_ = v___y_1686_;
v___y_1696_ = v___y_1687_;
goto v___jp_1689_;
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v_item_1681_);
lean_dec_ref(v_config_1680_);
v_a_2392_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_1700_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_1700_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
v___jp_1689_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1698_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1690_, v___x_1697_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2400_, lean_object* v_item_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2400_, v_item_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2412_, v___y_2416_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2448_, lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_msg_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2458_, v_msg_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2468_, lean_object* v_macroStack_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2468_, v_macroStack_2469_, v___y_2474_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2478_, lean_object* v_macroStack_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2478_, v_macroStack_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2487_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2490_ = l_Lean_mkConst(v___x_2489_, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2493_, lean_object* v_cfgItem_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2503_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2493_, v_cfgItem_2494_, v___x_2502_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2504_, lean_object* v_cfgItem_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2504_, v_cfgItem_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v_cfgItem_2505_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object* v_cfg_2515_, lean_object* v_init_2516_, uint8_t v_logExceptions_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_onErr_2522_; lean_object* v_eval_2523_; 
v_onErr_2522_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0));
v_eval_2523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2517_ == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2523_, v_init_2516_, v_cfg_2515_, v_onErr_2522_, v_logExceptions_2517_, v_a_2519_, v_a_2520_);
return v___x_2524_;
}
else
{
uint8_t v_recover_2525_; lean_object* v___x_2526_; 
v_recover_2525_ = lean_ctor_get_uint8(v_a_2518_, sizeof(void*)*1);
v___x_2526_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2523_, v_init_2516_, v_cfg_2515_, v_onErr_2522_, v_recover_2525_, v_a_2519_, v_a_2520_);
return v___x_2526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2527_, lean_object* v_init_2528_, lean_object* v_logExceptions_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
uint8_t v_logExceptions_boxed_2534_; lean_object* v_res_2535_; 
v_logExceptions_boxed_2534_ = lean_unbox(v_logExceptions_2529_);
v_res_2535_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2527_, v_init_2528_, v_logExceptions_boxed_2534_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object* v_cfg_2536_, lean_object* v_init_2537_, uint8_t v_logExceptions_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2536_, v_init_2537_, v_logExceptions_2538_, v_a_2539_, v_a_2545_, v_a_2546_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object* v_cfg_2549_, lean_object* v_init_2550_, lean_object* v_logExceptions_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
uint8_t v_logExceptions_boxed_2561_; lean_object* v_res_2562_; 
v_logExceptions_boxed_2561_ = lean_unbox(v_logExceptions_2551_);
v_res_2562_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2549_, v_init_2550_, v_logExceptions_boxed_2561_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_));
v___x_2576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_));
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_));
v___x_2578_ = l_Lean_Meta_registerSimpAttr(v___x_2575_, v___x_2576_, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_();
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_2600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_2601_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_2598_, v___x_2599_, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_2616_ = l_Lean_Meta_registerSimpAttr(v___x_2613_, v___x_2614_, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object* v_e_2619_){
_start:
{
if (lean_obj_tag(v_e_2619_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
v_a_2621_ = lean_ctor_get(v_e_2619_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_e_2619_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2623_ = v_e_2619_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v_e_2619_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_mk_io_user_error(v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 1);
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_a_2630_ = lean_ctor_get(v_e_2619_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_e_2619_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v_e_2619_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v_e_2619_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 0);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_e_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2641_, lean_object* v_e_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2645_, lean_object* v_e_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(v_00_u03b1_2645_, v_e_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v_declName_2649_, lean_object* v_stx_2650_, uint8_t v_attrKind_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v_env_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2655_ = lean_st_ref_get(v___y_2653_);
v_env_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_ref_n(v_env_2656_, 2);
lean_dec(v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_2658_ = l_Lean_getAttributeImpl(v_env_2656_, v___x_2657_);
v___x_2659_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_add_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v_add_2661_ = lean_ctor_get(v_a_2660_, 1);
lean_inc_ref(v_add_2661_);
lean_dec(v_a_2660_);
v___x_2662_ = lean_box(v_attrKind_2651_);
lean_inc(v___y_2653_);
lean_inc_ref(v___y_2652_);
lean_inc(v_stx_2650_);
lean_inc(v_declName_2649_);
v___x_2663_ = lean_apply_6(v_add_2661_, v_declName_2649_, v_stx_2650_, v___x_2662_, v___y_2652_, v___y_2653_, lean_box(0));
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2689_; 
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2663_, 0);
lean_dec(v_unused_2690_);
v___x_2665_ = v___x_2663_;
v_isShared_2666_ = v_isSharedCheck_2689_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v___x_2663_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2689_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_2668_ = l_Lean_getAttributeImpl(v_env_2656_, v___x_2667_);
v___x_2669_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v_add_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_del_object(v___x_2665_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v_add_2671_ = lean_ctor_get(v_a_2670_, 1);
lean_inc_ref(v_add_2671_);
lean_dec(v_a_2670_);
v___x_2672_ = lean_box(v_attrKind_2651_);
lean_inc(v___y_2653_);
lean_inc_ref(v___y_2652_);
v___x_2673_ = lean_apply_6(v_add_2671_, v_declName_2649_, v_stx_2650_, v___x_2672_, v___y_2652_, v___y_2653_, lean_box(0));
return v___x_2673_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_stx_2650_);
lean_dec(v_declName_2649_);
v_a_2674_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2676_ = v___x_2669_;
v_isShared_2677_ = v_isSharedCheck_2688_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2669_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2688_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_ref_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v_ref_2678_ = lean_ctor_get(v___y_2652_, 5);
v___x_2679_ = lean_io_error_to_string(v_a_2674_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 3);
lean_ctor_set(v___x_2665_, 0, v___x_2679_);
v___x_2681_ = v___x_2665_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2682_ = l_Lean_MessageData_ofFormat(v___x_2681_);
lean_inc(v_ref_2678_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_ref_2678_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2683_);
v___x_2685_ = v___x_2676_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
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
}
}
else
{
lean_dec_ref(v_env_2656_);
lean_dec(v_stx_2650_);
lean_dec(v_declName_2649_);
return v___x_2663_;
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_env_2656_);
lean_dec(v_stx_2650_);
lean_dec(v_declName_2649_);
v_a_2691_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2693_ = v___x_2659_;
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2659_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_ref_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v_ref_2695_ = lean_ctor_get(v___y_2652_, 5);
v___x_2696_ = lean_io_error_to_string(v_a_2691_);
v___x_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_ofFormat(v___x_2697_);
lean_inc(v_ref_2695_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_ref_2695_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2699_);
v___x_2701_ = v___x_2693_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_declName_2704_, lean_object* v_stx_2705_, lean_object* v_attrKind_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_attrKind_boxed_2710_; lean_object* v_res_2711_; 
v_attrKind_boxed_2710_ = lean_unbox(v_attrKind_2706_);
v_res_2711_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_2704_, v_stx_2705_, v_attrKind_boxed_2710_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2711_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
lean_ctor_set(v___x_2717_, 3, v___x_2716_);
lean_ctor_set(v___x_2717_, 4, v___x_2715_);
lean_ctor_set(v___x_2717_, 5, v___x_2715_);
lean_ctor_set(v___x_2717_, 6, v___x_2715_);
lean_ctor_set(v___x_2717_, 7, v___x_2715_);
lean_ctor_set(v___x_2717_, 8, v___x_2715_);
lean_ctor_set(v___x_2717_, 9, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_unsigned_to_nat(32u);
v___x_2719_ = lean_mk_empty_array_with_capacity(v___x_2718_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2721_ = ((size_t)5ULL);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = lean_unsigned_to_nat(32u);
v___x_2724_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2725_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_2726_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
lean_ctor_set(v___x_2726_, 1, v___x_2724_);
lean_ctor_set(v___x_2726_, 2, v___x_2722_);
lean_ctor_set(v___x_2726_, 3, v___x_2722_);
lean_ctor_set_usize(v___x_2726_, 4, v___x_2721_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2727_ = lean_box(1);
v___x_2728_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_2729_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_2730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2728_);
lean_ctor_set(v___x_2730_, 2, v___x_2727_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v_env_2736_; lean_object* v_options_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2735_ = lean_st_ref_get(v___y_2733_);
v_env_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2735_);
v_options_2737_ = lean_ctor_get(v___y_2732_, 2);
v___x_2738_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_2739_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_2737_);
v___x_2740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2740_, 0, v_env_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2738_);
lean_ctor_set(v___x_2740_, 2, v___x_2739_);
lean_ctor_set(v___x_2740_, 3, v_options_2737_);
v___x_2741_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_msgData_2731_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1(v_msgData_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_ref_2752_; lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_ref_2752_ = lean_ctor_get(v___y_2749_, 5);
v___x_2753_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1(v_msg_2748_, v___y_2749_, v___y_2750_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
lean_inc(v_ref_2752_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v_ref_2752_);
lean_ctor_set(v___x_2758_, 1, v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 1);
lean_ctor_set(v___x_2756_, 0, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v_msg_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_2770_ = l_Lean_stringToMessageData(v___x_2769_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_2773_ = l_Lean_stringToMessageData(v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v___x_2774_, lean_object* v_decl_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_2780_ = l_Lean_MessageData_ofName(v___x_2774_);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v___x_2783_, v___y_2776_, v___y_2777_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v___x_2785_, lean_object* v_decl_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_2785_, v_decl_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v_decl_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_2821_ = l_Lean_registerBuiltinAttribute(v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_2824_, lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v_msg_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_msg_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1(v_00_u03b1_2830_, v_msg_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2835_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2836_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1);
return v___x_2840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_2842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_);
v___x_2844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_);
v___x_2845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
lean_ctor_set(v___x_2845_, 2, v___x_2843_);
lean_ctor_set(v___x_2845_, 3, v___x_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_);
v___x_2848_ = lean_st_mk_ref(v___x_2847_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_();
return v_res_2851_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Lean_Meta_Tactic_BVDecide_builtinBVNormalizeSimprocsRef;
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_));
v___x_2867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_));
v___x_2868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_);
v___x_2869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_));
v___x_2870_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_2866_, v___x_2867_, v___x_2868_, v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_();
return v_res_2872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0));
v___x_2875_ = l_Lean_stringToMessageData(v___x_2874_);
return v___x_2875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2));
v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2884_ = l_Lean_stringToMessageData(v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2890_ = l_Lean_stringToMessageData(v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2893_ = l_Lean_stringToMessageData(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2894_, lean_object* v_declHint_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_env_2899_; uint8_t v___y_2901_; uint8_t v___x_2957_; uint8_t v___x_2958_; 
v___x_2898_ = lean_st_ref_get(v___y_2896_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2957_ = l_Lean_Name_isAnonymous(v_declHint_2895_);
v___x_2958_ = lean_bool_not(v___x_2957_);
if (v___x_2958_ == 0)
{
v___y_2901_ = v___x_2958_;
goto v___jp_2900_;
}
else
{
uint8_t v_isExporting_2959_; 
v_isExporting_2959_ = lean_ctor_get_uint8(v_env_2899_, sizeof(void*)*8);
v___y_2901_ = v_isExporting_2959_;
goto v___jp_2900_;
}
v___jp_2900_:
{
if (v___y_2901_ == 0)
{
lean_object* v___x_2902_; 
lean_dec_ref(v_env_2899_);
lean_dec(v_declHint_2895_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_msg_2894_);
return v___x_2902_;
}
else
{
uint8_t v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = 0;
lean_inc_ref(v_env_2899_);
v___x_2904_ = l_Lean_Environment_setExporting(v_env_2899_, v___x_2903_);
lean_inc(v_declHint_2895_);
lean_inc_ref(v___x_2904_);
v___x_2905_ = l_Lean_Environment_contains(v___x_2904_, v_declHint_2895_, v___y_2901_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_env_2899_);
lean_dec(v_declHint_2895_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_msg_2894_);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v_c_2912_; lean_object* v___x_2913_; 
v___x_2907_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_2908_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1_spec__1___closed__5);
v___x_2909_ = l_Lean_Options_empty;
v___x_2910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2904_);
lean_ctor_set(v___x_2910_, 1, v___x_2907_);
lean_ctor_set(v___x_2910_, 2, v___x_2908_);
lean_ctor_set(v___x_2910_, 3, v___x_2909_);
lean_inc(v_declHint_2895_);
v___x_2911_ = l_Lean_MessageData_ofConstName(v_declHint_2895_, v___x_2903_);
v_c_2912_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2912_, 0, v___x_2910_);
lean_ctor_set(v_c_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2899_, v_declHint_2895_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v_env_2899_);
lean_dec(v_declHint_2895_);
v___x_2914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v_c_2912_);
v___x_2916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = l_Lean_MessageData_note(v___x_2917_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v_msg_2894_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
else
{
lean_object* v_val_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2956_; 
v_val_2921_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2923_ = v___x_2913_;
v_isShared_2924_ = v_isSharedCheck_2956_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_val_2921_);
lean_dec(v___x_2913_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2956_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v_mod_2928_; uint8_t v___x_2929_; 
v___x_2925_ = lean_box(0);
v___x_2926_ = l_Lean_Environment_header(v_env_2899_);
lean_dec_ref(v_env_2899_);
v___x_2927_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2926_);
v_mod_2928_ = lean_array_get(v___x_2925_, v___x_2927_, v_val_2921_);
lean_dec(v_val_2921_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = l_Lean_isPrivateName(v_declHint_2895_);
lean_dec(v_declHint_2895_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v_c_2912_);
v___x_2932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l_Lean_MessageData_ofName(v_mod_2928_);
v___x_2935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2933_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = l_Lean_MessageData_note(v___x_2937_);
v___x_2939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_msg_2894_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2939_);
v___x_2941_ = v___x_2923_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v_c_2912_);
v___x_2945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = l_Lean_MessageData_ofName(v_mod_2928_);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_MessageData_note(v___x_2950_);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_msg_2894_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2952_);
v___x_2954_ = v___x_2923_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2960_, lean_object* v_declHint_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2960_, v_declHint_2961_, v___y_2962_);
lean_dec(v___y_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2965_, lean_object* v_declHint_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2980_; 
v___x_2970_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2965_, v_declHint_2966_, v___y_2968_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2975_ = l_Lean_unknownIdentifierMessageTag;
v___x_2976_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_a_2971_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2976_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2981_, lean_object* v_declHint_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2981_, v_declHint_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2987_, lean_object* v_msg_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_fileName_2992_; lean_object* v_fileMap_2993_; lean_object* v_options_2994_; lean_object* v_currRecDepth_2995_; lean_object* v_maxRecDepth_2996_; lean_object* v_ref_2997_; lean_object* v_currNamespace_2998_; lean_object* v_openDecls_2999_; lean_object* v_initHeartbeats_3000_; lean_object* v_maxHeartbeats_3001_; lean_object* v_quotContext_3002_; lean_object* v_currMacroScope_3003_; uint8_t v_diag_3004_; lean_object* v_cancelTk_x3f_3005_; uint8_t v_suppressElabErrors_3006_; lean_object* v_inheritedTraceOptions_3007_; lean_object* v_ref_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_fileName_2992_ = lean_ctor_get(v___y_2989_, 0);
v_fileMap_2993_ = lean_ctor_get(v___y_2989_, 1);
v_options_2994_ = lean_ctor_get(v___y_2989_, 2);
v_currRecDepth_2995_ = lean_ctor_get(v___y_2989_, 3);
v_maxRecDepth_2996_ = lean_ctor_get(v___y_2989_, 4);
v_ref_2997_ = lean_ctor_get(v___y_2989_, 5);
v_currNamespace_2998_ = lean_ctor_get(v___y_2989_, 6);
v_openDecls_2999_ = lean_ctor_get(v___y_2989_, 7);
v_initHeartbeats_3000_ = lean_ctor_get(v___y_2989_, 8);
v_maxHeartbeats_3001_ = lean_ctor_get(v___y_2989_, 9);
v_quotContext_3002_ = lean_ctor_get(v___y_2989_, 10);
v_currMacroScope_3003_ = lean_ctor_get(v___y_2989_, 11);
v_diag_3004_ = lean_ctor_get_uint8(v___y_2989_, sizeof(void*)*14);
v_cancelTk_x3f_3005_ = lean_ctor_get(v___y_2989_, 12);
v_suppressElabErrors_3006_ = lean_ctor_get_uint8(v___y_2989_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3007_ = lean_ctor_get(v___y_2989_, 13);
v_ref_3008_ = l_Lean_replaceRef(v_ref_2987_, v_ref_2997_);
lean_inc_ref(v_inheritedTraceOptions_3007_);
lean_inc(v_cancelTk_x3f_3005_);
lean_inc(v_currMacroScope_3003_);
lean_inc(v_quotContext_3002_);
lean_inc(v_maxHeartbeats_3001_);
lean_inc(v_initHeartbeats_3000_);
lean_inc(v_openDecls_2999_);
lean_inc(v_currNamespace_2998_);
lean_inc(v_maxRecDepth_2996_);
lean_inc(v_currRecDepth_2995_);
lean_inc_ref(v_options_2994_);
lean_inc_ref(v_fileMap_2993_);
lean_inc_ref(v_fileName_2992_);
v___x_3009_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3009_, 0, v_fileName_2992_);
lean_ctor_set(v___x_3009_, 1, v_fileMap_2993_);
lean_ctor_set(v___x_3009_, 2, v_options_2994_);
lean_ctor_set(v___x_3009_, 3, v_currRecDepth_2995_);
lean_ctor_set(v___x_3009_, 4, v_maxRecDepth_2996_);
lean_ctor_set(v___x_3009_, 5, v_ref_3008_);
lean_ctor_set(v___x_3009_, 6, v_currNamespace_2998_);
lean_ctor_set(v___x_3009_, 7, v_openDecls_2999_);
lean_ctor_set(v___x_3009_, 8, v_initHeartbeats_3000_);
lean_ctor_set(v___x_3009_, 9, v_maxHeartbeats_3001_);
lean_ctor_set(v___x_3009_, 10, v_quotContext_3002_);
lean_ctor_set(v___x_3009_, 11, v_currMacroScope_3003_);
lean_ctor_set(v___x_3009_, 12, v_cancelTk_x3f_3005_);
lean_ctor_set(v___x_3009_, 13, v_inheritedTraceOptions_3007_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*14, v_diag_3004_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*14 + 1, v_suppressElabErrors_3006_);
v___x_3010_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v_msg_2988_, v___x_3009_, v___y_2990_);
lean_dec_ref_known(v___x_3009_, 14);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3011_, v_msg_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v_ref_3011_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_3017_, lean_object* v_msg_3018_, lean_object* v_declHint_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; lean_object* v_a_3024_; lean_object* v___x_3025_; 
v___x_3023_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3018_, v_declHint_3019_, v___y_3020_, v___y_3021_);
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref(v___x_3023_);
v___x_3025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3017_, v_a_3024_, v___y_3020_, v___y_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_3026_, lean_object* v_msg_3027_, lean_object* v_declHint_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3026_, v_msg_3027_, v_declHint_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v_ref_3026_);
return v_res_3032_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3036_, lean_object* v_constName_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3041_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3042_ = 0;
lean_inc(v_constName_3037_);
v___x_3043_ = l_Lean_MessageData_ofConstName(v_constName_3037_, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3041_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3036_, v___x_3046_, v_constName_3037_, v___y_3038_, v___y_3039_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3048_, lean_object* v_constName_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg(v_ref_3048_, v_constName_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v_ref_3048_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg(lean_object* v_constName_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_ref_3058_; lean_object* v___x_3059_; 
v_ref_3058_ = lean_ctor_get(v___y_3055_, 5);
v___x_3059_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg(v_ref_3058_, v_constName_3054_, v___y_3055_, v___y_3056_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg(v_constName_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0(lean_object* v_constName_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; lean_object* v_env_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = lean_st_ref_get(v___y_3067_);
v_env_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc_ref(v_env_3070_);
lean_dec(v___x_3069_);
v___x_3071_ = 0;
lean_inc(v_constName_3065_);
v___x_3072_ = l_Lean_Environment_find_x3f(v_env_3070_, v_constName_3065_, v___x_3071_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg(v_constName_3065_, v___y_3066_, v___y_3067_);
return v___x_3073_;
}
else
{
lean_object* v_val_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_constName_3065_);
v_val_3074_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3072_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_val_3074_);
lean_dec(v___x_3072_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 0);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_val_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0___boxed(lean_object* v_constName_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0(v_constName_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__4));
v___x_3097_ = l_Lean_mkConst(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__7));
v___x_3104_ = l_Lean_mkConst(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__9));
v___x_3107_ = l_Lean_stringToMessageData(v___x_3106_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = l_Lean_Level_ofNat(v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16);
v___x_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__17);
v___x_3121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__16);
v___x_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__18);
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__15));
v___x_3125_ = l_Lean_mkConst(v___x_3124_, v___x_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_box(0);
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__20));
v___x_3133_ = l_Lean_mkConst(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_box(0);
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__23));
v___x_3142_ = l_Lean_mkConst(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin(lean_object* v_declName_3150_, lean_object* v_stx_3151_, lean_object* v_addDeclName_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; uint8_t v___y_3183_; lean_object* v_procExpr_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3207_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3243_ = l_Lean_Syntax_getArg(v_stx_3151_, v___x_3242_);
v___x_3244_ = l_Lean_Syntax_isNone(v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = l_Lean_Syntax_getArg(v___x_3243_, v___x_3245_);
lean_dec(v___x_3243_);
v___x_3247_ = l_Lean_Syntax_getKind(v___x_3246_);
v___x_3248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__27));
v___x_3249_ = lean_name_eq(v___x_3247_, v___x_3248_);
lean_dec(v___x_3247_);
v___y_3207_ = v___x_3249_;
goto v___jp_3206_;
}
else
{
lean_dec(v___x_3243_);
v___y_3207_ = v___x_3244_;
goto v___jp_3206_;
}
v___jp_3156_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__1));
v___x_3164_ = l_Lean_Name_append(v_declName_3150_, v___x_3163_);
v___x_3165_ = l_Lean_Core_mkFreshUserName(v___x_3164_, v___y_3161_, v___y_3157_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = lean_unsigned_to_nat(3u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_array_push(v___x_3168_, v___y_3160_);
lean_inc_ref(v___y_3162_);
v___x_3170_ = lean_array_push(v___x_3169_, v___y_3162_);
v___x_3171_ = lean_array_push(v___x_3170_, v___y_3158_);
v___x_3172_ = l_Lean_mkAppN(v___y_3159_, v___x_3171_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = l_Lean_declareBuiltin(v_a_3166_, v___x_3172_, v___y_3161_, v___y_3157_);
return v___x_3173_;
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3158_);
v_a_3174_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3165_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3165_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
v___jp_3182_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_box(0);
v___x_3188_ = l_Lean_mkConst(v_addDeclName_3152_, v___x_3187_);
lean_inc(v_declName_3150_);
v___x_3189_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3150_);
if (v___y_3183_ == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__5);
v___y_3157_ = v___y_3186_;
v___y_3158_ = v_procExpr_3184_;
v___y_3159_ = v___x_3188_;
v___y_3160_ = v___x_3189_;
v___y_3161_ = v___y_3185_;
v___y_3162_ = v___x_3190_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__8);
v___y_3157_ = v___y_3186_;
v___y_3158_ = v_procExpr_3184_;
v___y_3159_ = v___x_3188_;
v___y_3160_ = v___x_3189_;
v___y_3161_ = v___y_3185_;
v___y_3162_ = v___x_3191_;
goto v___jp_3156_;
}
}
v___jp_3192_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v___x_3196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__10);
v___x_3197_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v___x_3196_, v___y_3194_, v___y_3195_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
v___jp_3206_:
{
lean_object* v___x_3208_; 
lean_inc(v_declName_3150_);
v___x_3208_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0(v_declName_3150_, v_a_3153_, v_a_3154_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_ConstantInfo_type(v_a_3209_);
lean_dec(v_a_3209_);
if (lean_obj_tag(v___x_3210_) == 4)
{
lean_object* v_declName_3211_; 
v_declName_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_declName_3211_);
lean_dec_ref_known(v___x_3210_, 2);
if (lean_obj_tag(v_declName_3211_) == 1)
{
lean_object* v_pre_3212_; 
v_pre_3212_ = lean_ctor_get(v_declName_3211_, 0);
lean_inc(v_pre_3212_);
if (lean_obj_tag(v_pre_3212_) == 1)
{
lean_object* v_pre_3213_; 
v_pre_3213_ = lean_ctor_get(v_pre_3212_, 0);
lean_inc(v_pre_3213_);
if (lean_obj_tag(v_pre_3213_) == 1)
{
lean_object* v_pre_3214_; 
v_pre_3214_ = lean_ctor_get(v_pre_3213_, 0);
lean_inc(v_pre_3214_);
if (lean_obj_tag(v_pre_3214_) == 1)
{
lean_object* v_pre_3215_; 
v_pre_3215_ = lean_ctor_get(v_pre_3214_, 0);
if (lean_obj_tag(v_pre_3215_) == 0)
{
lean_object* v_str_3216_; lean_object* v_str_3217_; lean_object* v_str_3218_; lean_object* v_str_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_str_3216_ = lean_ctor_get(v_declName_3211_, 1);
lean_inc_ref(v_str_3216_);
lean_dec_ref_known(v_declName_3211_, 2);
v_str_3217_ = lean_ctor_get(v_pre_3212_, 1);
lean_inc_ref(v_str_3217_);
lean_dec_ref_known(v_pre_3212_, 2);
v_str_3218_ = lean_ctor_get(v_pre_3213_, 1);
lean_inc_ref(v_str_3218_);
lean_dec_ref_known(v_pre_3213_, 2);
v_str_3219_ = lean_ctor_get(v_pre_3214_, 1);
lean_inc_ref(v_str_3219_);
lean_dec_ref_known(v_pre_3214_, 2);
v___x_3220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_3221_ = lean_string_dec_eq(v_str_3219_, v___x_3220_);
lean_dec_ref(v_str_3219_);
if (v___x_3221_ == 0)
{
lean_dec_ref(v_str_3218_);
lean_dec_ref(v_str_3217_);
lean_dec_ref(v_str_3216_);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_3223_ = lean_string_dec_eq(v_str_3218_, v___x_3222_);
lean_dec_ref(v_str_3218_);
if (v___x_3223_ == 0)
{
lean_dec_ref(v_str_3217_);
lean_dec_ref(v_str_3216_);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__11));
v___x_3225_ = lean_string_dec_eq(v_str_3217_, v___x_3224_);
lean_dec_ref(v_str_3217_);
if (v___x_3225_ == 0)
{
lean_dec_ref(v_str_3216_);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__12));
v___x_3227_ = lean_string_dec_eq(v_str_3216_, v___x_3226_);
lean_dec_ref(v_str_3216_);
if (v___x_3227_ == 0)
{
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__19);
v___x_3230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__21);
v___x_3231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___closed__24);
lean_inc(v_declName_3150_);
v___x_3232_ = l_Lean_mkConst(v_declName_3150_, v___x_3228_);
v___x_3233_ = l_Lean_mkApp3(v___x_3229_, v___x_3230_, v___x_3231_, v___x_3232_);
v___y_3183_ = v___y_3207_;
v_procExpr_3184_ = v___x_3233_;
v___y_3185_ = v_a_3153_;
v___y_3186_ = v_a_3154_;
goto v___jp_3182_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3214_, 2);
lean_dec_ref_known(v_pre_3213_, 2);
lean_dec_ref_known(v_pre_3212_, 2);
lean_dec_ref_known(v_declName_3211_, 2);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_dec_ref_known(v_pre_3213_, 2);
lean_dec(v_pre_3214_);
lean_dec_ref_known(v_pre_3212_, 2);
lean_dec_ref_known(v_declName_3211_, 2);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_dec_ref_known(v_pre_3212_, 2);
lean_dec(v_pre_3213_);
lean_dec_ref_known(v_declName_3211_, 2);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_dec(v_pre_3212_);
lean_dec_ref_known(v_declName_3211_, 2);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_dec(v_declName_3211_);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_dec_ref(v___x_3210_);
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v___y_3193_ = v___y_3207_;
v___y_3194_ = v_a_3153_;
v___y_3195_ = v_a_3154_;
goto v___jp_3192_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_addDeclName_3152_);
lean_dec(v_declName_3150_);
v_a_3234_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3208_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3208_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin___boxed(lean_object* v_declName_3250_, lean_object* v_stx_3251_, lean_object* v_addDeclName_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin(v_declName_3250_, v_stx_3251_, v_addDeclName_3252_, v_a_3253_, v_a_3254_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec(v_stx_3251_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0(lean_object* v_00_u03b1_3257_, lean_object* v_constName_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___redArg(v_constName_3258_, v___y_3259_, v___y_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3263_, lean_object* v_constName_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0(v_00_u03b1_3263_, v_constName_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3269_, lean_object* v_ref_3270_, lean_object* v_constName_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___redArg(v_ref_3270_, v_constName_3271_, v___y_3272_, v___y_3273_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3276_, lean_object* v_ref_3277_, lean_object* v_constName_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1(v_00_u03b1_3276_, v_ref_3277_, v_constName_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v_ref_3277_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3283_, lean_object* v_ref_3284_, lean_object* v_msg_3285_, lean_object* v_declHint_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3284_, v_msg_3285_, v_declHint_3286_, v___y_3287_, v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3291_, lean_object* v_ref_3292_, lean_object* v_msg_3293_, lean_object* v_declHint_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3291_, v_ref_3292_, v_msg_3293_, v_declHint_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v_ref_3292_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_3299_, lean_object* v_declHint_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3299_, v_declHint_3300_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_3305_, lean_object* v_declHint_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3305_, v_declHint_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3311_, lean_object* v_ref_3312_, lean_object* v_msg_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3312_, v_msg_3313_, v___y_3314_, v___y_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3318_, lean_object* v_ref_3319_, lean_object* v_msg_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3318_, v_ref_3319_, v_msg_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v_ref_3319_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object* v_declName_3325_, uint8_t v_post_3326_, lean_object* v_proc_3327_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = l_Lean_Meta_Tactic_BVDecide_builtinBVNormalizeSimprocsRef;
v___x_3330_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_3329_, v_declName_3325_, v_post_3326_, v_proc_3327_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object* v_declName_3331_, lean_object* v_post_3332_, lean_object* v_proc_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v_post_boxed_3335_; lean_object* v_res_3336_; 
v_post_boxed_3335_ = lean_unbox(v_post_3332_);
v_res_3336_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(v_declName_3331_, v_post_boxed_3335_, v_proc_3333_);
return v_res_3336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_));
v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(lean_object* v_x_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_);
v___x_3345_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__1___redArg(v___x_3344_, v___y_3341_, v___y_3342_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object* v_x_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(v_x_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v_x_3346_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(lean_object* v___x_3353_, lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v_declName_3356_, lean_object* v_stx_3357_, uint8_t v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0));
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_));
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_));
v___x_3365_ = l_Lean_Name_mkStr6(v___x_3353_, v___x_3362_, v___x_3354_, v___x_3355_, v___x_3363_, v___x_3364_);
v___x_3366_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_addBuiltin(v_declName_3356_, v_stx_3357_, v___x_3365_, v___y_3359_, v___y_3360_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_declName_3370_, lean_object* v_stx_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v_x_160__boxed_3376_; lean_object* v_res_3377_; 
v_x_160__boxed_3376_ = lean_unbox(v_x_3372_);
v_res_3377_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(v___x_3367_, v___x_3368_, v___x_3369_, v_declName_3370_, v_stx_3371_, v_x_160__boxed_3376_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v_stx_3371_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_));
v___x_3410_ = l_Lean_registerBuiltinAttribute(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2____boxed(lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_();
return v_res_3412_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_sat_solver = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_sat_solver);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode = _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode);
l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode = _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode);
l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig = _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3513353098____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_symIntToBitVecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2011030299____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_builtinBVNormalizeSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_builtinBVNormalizeSimprocsRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2218032216____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1562260944____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
